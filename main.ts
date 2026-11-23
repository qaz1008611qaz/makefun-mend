// mend: apply an AI-written edit to a tree of text files.
//
// A patch comes in one of four shapes: a unified diff (whose line numbers the
// model may have got wrong), SEARCH/REPLACE blocks, a V4A patch, or JSON tool
// calls. mend finds the lines each edit names, allowing for drifted
// whitespace, and writes every change or none. SPEC.md is the contract this
// file implements; it runs on Node 22 with the standard library alone.
//
// Usage: node main.ts [--format=NAME] [--check] [--strict] [PATCH]
// When MAKEFUN_ENV_URL is set, the file hands a trial over to runner.ts.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

// A parse fault carries the patch line it is reported at.
class ParseErr {
  constructor(line) { this.line = line; }
}
// A failed edit carries its code and the path it concerns.
class EditFail {
  constructor(code, path) { this.code = code; this.path = path; }
}

function blank(s) { return s.trim() === ''; }
function trimSp(s) { return s.replace(/^ +/, '').replace(/ +$/, ''); }

function isSafe(p) {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') &&
    p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

// A patch's lines: split at \n, one trailing \r off each, no empty piece
// after a final \n.
function splitPatch(text) {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

// A file as lines: its break, its lines, whether it ends with a break.
function parseText(text) {
  if (text === '') return { br: '\n', lines: [], fin: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const fin = text.endsWith(br);
  if (fin) parts.pop();
  return { br, lines: parts, fin };
}
function renderText(f) {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.fin ? f.br : '');
}

function leadWs(s) {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
}

// How a line compares at a tier: exact, trailing whitespace off, or both
// ends off.
function keyFor(s, tier) {
  if (tier === 0) return s;
  if (tier === 1) return s.replace(/[ \t]+$/, '');
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

// A replacement line at tier 2 takes the file's indent in place of the
// patch's, where it carries the patch's indent at all.
function reindent(line, pLead, fLead) {
  if (line === '' || /^[ \t]+$/.test(line)) return line;
  if (line.startsWith(pLead)) return fLead + line.slice(pLead.length);
  return line;
}

// The tree as the edits leave it. `cur` holds what changed; anything else
// is read from disk the first time it is needed.
class Tree {
  constructor() {
    this.disk = new Map();
    this.cur = new Map();
  }
  orig(p) {
    if (!this.disk.has(p)) {
      let v = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch { v = null; }
      this.disk.set(p, v);
    }
    return this.disk.get(p);
  }
  read(p) {
    return this.cur.has(p) ? this.cur.get(p) : this.orig(p);
  }
  set(p, v) { this.cur.set(p, v); }
}

// Occurrences of needle in lines at or after `from`, at the first tier with
// one. Tiers are tried in order, and only tier 0 when strict.
function firstTierFrom(lines, needle, strict, from) {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const occ = [];
    for (let i = from; i + needle.length <= lines.length; i += 1) {
      let ok = true;
      for (let j = 0; j < needle.length; j += 1) {
        if (keyFor(lines[i + j], t) !== keyFor(needle[j], t)) { ok = false; break; }
      }
      if (ok) occ.push(i);
    }
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}

// The first line at or after `from` equal to a single-line anchor, at the
// first tier with one; -1 when there is none.
function findAnchor(lines, anchor, from, strict) {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    for (let i = from; i < lines.length; i += 1) {
      if (keyFor(lines[i], t) === keyFor(anchor, t)) return i;
    }
  }
  return -1;
}

// The lines a replacement writes: context lines as the file's own matched
// lines, other lines re-indented at tier 2 and as written otherwise.
function buildRep(nList, file, start, tier, oFirst) {
  const fLead = leadWs(file.lines[start]);
  const pLead = leadWs(oFirst);
  return nList.map((e) => {
    if (e.c) return file.lines[start + e.oi];
    if (tier === 2) return reindent(e.t, pLead, fLead);
    return e.t;
  });
}

// Apply one hunk to a file: null when its old lines are nowhere in it.
// `a` is the hunk header's old start line, `d` the drift of the hunks
// before it in this section.
function applyHunk(file, hunk, a, d, strict) {
  const o = hunk.oLines;
  if (o.length === 0) {
    const at = Math.max(0, Math.min(a + d, file.lines.length));
    const ins = hunk.nList.map((e) => e.t);
    const lines = file.lines.slice(0, at).concat(ins, file.lines.slice(at));
    const fin = at === file.lines.length ? !hunk.markAfterLast : file.fin;
    return { br: file.br, lines, fin };
  }
  const found = firstTierFrom(file.lines, o, strict, 0);
  if (found === null) return null;
  const want = a - 1 + d;
  let best = found.occ[0];
  for (const p of found.occ) {
    if (Math.abs(p - want) < Math.abs(best - want)) best = p;
  }
  const rep = buildRep(hunk.nList, file, best, found.tier, o[0]);
  const lines = file.lines.slice(0, best).concat(rep, file.lines.slice(best + o.length));
  const fin = best + o.length === file.lines.length ? !hunk.markAfterLast : file.fin;
  return { br: file.br, lines, fin };
}

// ---- unified diffs (SPEC.md section 6) ----

// The path a --- or +++ header line names, or null for /dev/null.
function headerPathText(line) {
  let s = line.slice(4);
  const tab = s.indexOf('\t');
  if (tab >= 0) s = s.slice(0, tab);
  s = trimSp(s);
  if (s === '/dev/null') return null;
  if (s.startsWith('a/') || s.startsWith('b/')) s = s.slice(2);
  return s;
}

// One hunk: its old start line, its old lines, its new lines (each marked
// context or added, with a context line's place in the old lines), and
// whether a backslash line follows its last context or added line.
function parseHunk(lines, i) {
  const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(lines[i]);
  if (!m) throw new ParseErr(i + 1);
  const a = parseInt(m[1], 10);
  let j = i + 1;
  const body = [];
  while (j < lines.length) {
    const l = lines[j];
    if (l.startsWith('diff --git ')) break;
    if (l.startsWith('--- ') && j + 1 < lines.length && lines[j + 1].startsWith('+++ ')) break;
    if (l === '') { body.push({ k: 'c', t: '' }); j += 1; continue; }
    const c = l[0];
    if (c === ' ') { body.push({ k: 'c', t: l.slice(1) }); j += 1; continue; }
    if (c === '-') { body.push({ k: 'o', t: l.slice(1) }); j += 1; continue; }
    if (c === '+') { body.push({ k: 'n', t: l.slice(1) }); j += 1; continue; }
    if (c === '\\') { body.push({ k: 'm', t: l }); j += 1; continue; }
    break;
  }
  while (body.length > 0) {
    const last = body[body.length - 1];
    if (last.k === 'c' && last.t === '') body.pop();
    else break;
  }
  const oLines = [];
  const nList = [];
  for (const e of body) {
    if (e.k === 'c') { oLines.push(e.t); nList.push({ c: true, t: e.t, oi: oLines.length - 1 }); }
    else if (e.k === 'o') { oLines.push(e.t); }
    else if (e.k === 'n') { nList.push({ c: false, t: e.t }); }
  }
  let markAfterLast = false;
  let plusMark = false;
  for (let k = body.length - 1; k >= 0; k -= 1) {
    if (body[k].k === 'c' || body[k].k === 'n') {
      markAfterLast = k + 1 < body.length && body[k + 1].k === 'm';
      break;
    }
  }
  for (let k = body.length - 1; k >= 0; k -= 1) {
    if (body[k].k === 'n') {
      plusMark = k + 1 < body.length && body[k + 1].k === 'm';
      break;
    }
  }
  return { hunk: { a, oLines, nList, markAfterLast, plusMark }, next: j };
}

// Read one section's header and hunks starting at line i; returns the next
// line after the section.
function readSection(lines, i, sec) {
  const n = lines.length;
  while (i < n) {
    const l = lines[i];
    if (l.startsWith('@@')) break;
    if (l.startsWith('diff --git ')) break;
    if (l.startsWith('--- ')) {
      if (i + 1 < n && lines[i + 1].startsWith('+++ ')) {
        sec.pairOld = headerPathText(l);
        sec.pairNew = headerPathText(lines[i + 1]);
        i += 2;
        continue;
      }
      throw new ParseErr(i + 2);
    }
    if (l.startsWith('+++ ')) { sec.pairNew = headerPathText(l); i += 1; continue; }
    if (l.startsWith('rename from ')) { sec.renameFrom = trimSp(l.slice(12)); i += 1; continue; }
    if (l.startsWith('rename to ')) { sec.renameTo = trimSp(l.slice(10)); i += 1; continue; }
    if (l.startsWith('new file mode')) { sec.create = true; i += 1; continue; }
    if (l.startsWith('deleted file mode')) { sec.del = true; i += 1; continue; }
    i += 1;
  }
  while (i < n) {
    const l = lines[i];
    if (l.startsWith('diff --git ')) break;
    if (l.startsWith('--- ') && i + 1 < n && lines[i + 1].startsWith('+++ ')) break;
    if (l.startsWith('@@')) {
      const parsed = parseHunk(lines, i);
      sec.hunks.push(parsed.hunk);
      i = parsed.next;
      continue;
    }
    i += 1;
  }
  return i;
}

function sectionPath(sec, which) {
  if (which === 'old') {
    if (sec.pairOld !== undefined) return sec.pairOld;
    if (sec.renameFrom !== null) return sec.renameFrom;
    return sec.diffOld;
  }
  if (sec.pairNew !== undefined) return sec.pairNew;
  if (sec.renameTo !== null) return sec.renameTo;
  return sec.diffNew;
}

function makeUnifiedEdit(sec, strict) {
  const oldP = sectionPath(sec, 'old');
  const newP = sectionPath(sec, 'new');
  const create = sec.create || oldP === null;
  const del = sec.del || newP === null;
  return (tree, moves) => {
    if (oldP === null && newP === null) return;
    if (oldP !== null && !isSafe(oldP)) throw new EditFail('unsafe', oldP);
    if (newP !== null && !isSafe(newP)) throw new EditFail('unsafe', newP);
    if (create) {
      if (tree.read(newP) !== null) throw new EditFail('exists', newP);
      const plus = [];
      let mark = false;
      let seen = false;
      for (const h of sec.hunks) {
        for (const e of h.nList) if (!e.c) { plus.push(e.t); seen = true; }
        if (h.nList.some((e) => !e.c)) mark = h.plusMark;
      }
      tree.set(newP, renderText({ br: '\n', lines: plus, fin: seen && !mark }));
      return;
    }
    if (del) {
      if (tree.read(oldP) === null) throw new EditFail('missing', oldP);
      tree.set(oldP, null);
      return;
    }
    const applyAll = (startText) => {
      let f = parseText(startText);
      let d = 0;
      for (const h of sec.hunks) {
        const next = applyHunk(f, h, h.a, d, strict);
        if (next === null) throw new EditFail('no-match', oldP);
        d += h.nList.length - h.oLines.length;
        f = next;
      }
      return renderText(f);
    };
    if (oldP !== newP) {
      const cur = tree.read(oldP);
      if (cur === null) throw new EditFail('missing', oldP);
      if (tree.read(newP) !== null) throw new EditFail('exists', newP);
      const out = applyAll(cur);
      tree.set(oldP, null);
      tree.set(newP, out);
      moves.push([oldP, newP]);
      return;
    }
    const cur = tree.read(oldP);
    if (cur === null) throw new EditFail('missing', oldP);
    tree.set(oldP, applyAll(cur));
  };
}

function parseUnified(lines, strict) {
  const edits = [];
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const line = lines[i];
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)/.exec(line);
      if (!m) throw new ParseErr(i + 1);
      const sec = { pairOld: undefined, pairNew: undefined, renameFrom: null, renameTo: null, diffOld: m[1], diffNew: m[2], create: false, del: false, hunks: [] };
      i = readSection(lines, i + 1, sec);
      edits.push(makeUnifiedEdit(sec, strict));
    } else if (line.startsWith('--- ') && i + 1 < n && lines[i + 1].startsWith('+++ ')) {
      const sec = { pairOld: undefined, pairNew: undefined, renameFrom: null, renameTo: null, diffOld: null, diffNew: null, create: false, del: false, hunks: [] };
      i = readSection(lines, i, sec);
      edits.push(makeUnifiedEdit(sec, strict));
    } else if (line.startsWith('@@')) {
      // A hunk before any section, and any other line starting with @@.
      throw new ParseErr(i + 1);
    } else {
      i += 1;
    }
  }
  return edits;
}

// ---- SEARCH/REPLACE blocks (SPEC.md section 7) ----

function makeSearchReplaceEdit(path, oldLines, newLines, strict) {
  return (tree) => {
    if (!isSafe(path)) throw new EditFail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.read(path) !== null) throw new EditFail('exists', path);
      tree.set(path, renderText({ br: '\n', lines: newLines, fin: newLines.length > 0 }));
      return;
    }
    const cur = tree.read(path);
    if (cur === null) throw new EditFail('missing', path);
    const f = parseText(cur);
    const found = firstTierFrom(f.lines, oldLines, strict, 0);
    if (found === null) throw new EditFail('no-match', path);
    if (found.occ.length > 1) throw new EditFail('ambiguous', path);
    const start = found.occ[0];
    const rep = newLines.map((t) => (found.tier === 2 ? reindent(t, leadWs(oldLines[0]), leadWs(f.lines[start])) : t));
    const lines = f.lines.slice(0, start).concat(rep, f.lines.slice(start + oldLines.length));
    tree.set(path, renderText({ br: f.br, lines, fin: f.fin }));
  };
}

function parseSearchReplace(lines, strict) {
  const edits = [];
  let prevEnd = -1;
  let prevPath = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i].trimEnd() !== '<<<<<<< SEARCH') { i += 1; continue; }
    const searchAt = i;
    let path = null;
    for (let j = i - 1; j > prevEnd; j -= 1) {
      const t = lines[j].trim();
      if (t === '' || t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new ParseErr(searchAt + 1);
      path = prevPath;
    }
    let eq = -1;
    for (let j = i + 1; j < lines.length; j += 1) {
      if (lines[j].trimEnd() === '>>>>>>> REPLACE') throw new ParseErr(searchAt + 1);
      if (lines[j].trimEnd() === '=======') { eq = j; break; }
    }
    if (eq < 0) throw new ParseErr(searchAt + 1);
    let rep = -1;
    for (let j = eq + 1; j < lines.length; j += 1) {
      if (lines[j].trimEnd() === '>>>>>>> REPLACE') { rep = j; break; }
    }
    if (rep < 0) throw new ParseErr(searchAt + 1);
    edits.push(makeSearchReplaceEdit(path, lines.slice(i + 1, eq), lines.slice(eq + 1, rep), strict));
    prevPath = path;
    prevEnd = rep;
    i = rep + 1;
  }
  return edits;
}

// ---- V4A patches (SPEC.md section 8) ----

function v4aKind(l) {
  if (l.startsWith('*** Add File: ')) return 'add';
  if (l.startsWith('*** Delete File: ')) return 'delete';
  if (l.startsWith('*** Update File: ')) return 'update';
  return null;
}
function v4aPath(l) {
  return trimSp(l.slice(l.indexOf(': ') + 2));
}

function parseV4A(lines, strict) {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new ParseErr(1);
  if (lines[first].trim() !== '*** Begin Patch') throw new ParseErr(first + 1);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k -= 1) {
    if (!blank(lines[k])) { last = k; break; }
  }
  if (lines[last].trim() !== '*** End Patch') throw new ParseErr(lines.length + 1);
  const edits = [];
  let i = first + 1;
  while (i < last) {
    const l = lines[i];
    if (blank(l)) { i += 1; continue; }
    const kind = v4aKind(l);
    if (kind === null) throw new ParseErr(i + 1);
    let j = i + 1;
    while (j < last && v4aKind(lines[j]) === null) j += 1;
    const raw = [];
    for (let k = i + 1; k < j; k += 1) raw.push([k, lines[k]]);
    while (raw.length > 0 && blank(raw[raw.length - 1][1])) raw.pop();
    edits.push(makeV4AEdit(kind, v4aPath(l), raw, strict, i + 1));
    i = j;
  }
  return edits;
}

function makeV4AEdit(kind, path, raw, strict, startNo) {
  if (kind === 'add') {
    const fileLines = [];
    for (const [no, l] of raw) {
      if (blank(l)) fileLines.push('');
      else if (l.startsWith('+')) fileLines.push(l.slice(1));
      else throw new ParseErr(no + 1);
    }
    return (tree) => {
      if (!isSafe(path)) throw new EditFail('unsafe', path);
      if (tree.read(path) !== null) throw new EditFail('exists', path);
      tree.set(path, renderText({ br: '\n', lines: fileLines, fin: fileLines.length > 0 }));
    };
  }
  if (kind === 'delete') {
    for (const [no, l] of raw) {
      if (!blank(l)) throw new ParseErr(no + 1);
    }
    return (tree) => {
      if (!isSafe(path)) throw new EditFail('unsafe', path);
      if (tree.read(path) === null) throw new EditFail('missing', path);
      tree.set(path, null);
    };
  }
  // update: an optional Move to line, then chunks
  let k = 0;
  while (k < raw.length && blank(raw[k][1])) k += 1;
  let moveTo = null;
  if (k < raw.length && raw[k][1].startsWith('*** Move to: ')) {
    moveTo = trimSp(raw[k][1].slice(13));
    k += 1;
  }
  const chunks = [];
  let cur = null;
  const finish = () => { if (cur !== null) { chunks.push(cur); cur = null; } };
  while (k < raw.length) {
    const [no, l] = raw[k];
    if (blank(l)) {
      if (cur !== null) cur.body.push({ k: 'c', t: '' });
      k += 1;
      continue;
    }
    if (l.startsWith('@@')) {
      finish();
      cur = { anchor: trimSp(l.slice(2)) === '' ? null : trimSp(l.slice(2)), body: [], eof: false };
      k += 1;
      continue;
    }
    if (l.trim() === '*** End of File') {
      if (cur === null) throw new ParseErr(no + 1);
      cur.eof = true;
      finish();
      k += 1;
      continue;
    }
    const c = l[0];
    if (c === ' ' || c === '-' || c === '+') {
      if (cur === null) {
        if (chunks.length > 0) throw new ParseErr(no + 1);
        cur = { anchor: null, body: [], eof: false };
      }
      cur.body.push({ k: c === ' ' ? 'c' : c === '-' ? 'o' : 'n', t: l.slice(1) });
      k += 1;
      continue;
    }
    throw new ParseErr(no + 1);
  }
  finish();
  if (chunks.length === 0 && moveTo === null) throw new ParseErr(startNo);
  return (tree, moves) => {
    if (!isSafe(path)) throw new EditFail('unsafe', path);
    if (moveTo !== null && !isSafe(moveTo)) throw new EditFail('unsafe', moveTo);
    const curText = tree.read(path);
    if (curText === null) throw new EditFail('missing', path);
    if (moveTo !== null && tree.read(moveTo) !== null) throw new EditFail('exists', moveTo);
    let f = parseText(curText);
    let cursor = 0;
    for (const ch of chunks) {
      if (ch.anchor !== null) {
        const at = findAnchor(f.lines, ch.anchor, cursor, strict);
        if (at < 0) throw new EditFail('no-match', path);
        cursor = at + 1;
      }
      const o = [];
      const nList = [];
      for (const e of ch.body) {
        if (e.k === 'c') { o.push(e.t); nList.push({ c: true, t: e.t, oi: o.length - 1 }); }
        else if (e.k === 'o') { o.push(e.t); }
        else { nList.push({ c: false, t: e.t }); }
      }
      if (o.length === 0) {
        const at = ch.eof ? f.lines.length : cursor;
        const ins = nList.map((e) => e.t);
        f = { br: f.br, lines: f.lines.slice(0, at).concat(ins, f.lines.slice(at)), fin: f.fin };
        cursor = at + ins.length;
      } else {
        const found = firstTierFrom(f.lines, o, strict, cursor);
        if (found === null) throw new EditFail('no-match', path);
        let start = found.occ[0];
        if (ch.eof) {
          const good = found.occ.find((p) => p + o.length === f.lines.length);
          if (good === undefined) throw new EditFail('no-match', path);
          start = good;
        }
        const rep = buildRep(nList, f, start, found.tier, o[0]);
        f = { br: f.br, lines: f.lines.slice(0, start).concat(rep, f.lines.slice(start + o.length)), fin: f.fin };
        cursor = start + rep.length;
      }
    }
    const out = renderText(f);
    if (moveTo !== null) {
      tree.set(path, null);
      tree.set(moveTo, out);
      moves.push([path, moveTo]);
    } else {
      tree.set(path, out);
    }
  };
}

// ---- JSON edits (SPEC.md section 9) ----

function makeJsonEdit(v) {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const p = v.path;
  if (typeof p !== 'string') return null;
  if (v.command === 'create') {
    if (typeof v.file_text !== 'string') return null;
    const text = v.file_text;
    return (tree) => {
      if (!isSafe(p)) throw new EditFail('unsafe', p);
      if (tree.read(p) !== null) throw new EditFail('exists', p);
      tree.set(p, text);
    };
  }
  if (v.command === 'str_replace') {
    if (typeof v.old_str !== 'string' || v.old_str === '') return null;
    if (v.new_str !== undefined && typeof v.new_str !== 'string') return null;
    const oldStr = v.old_str;
    const newStr = v.new_str === undefined ? '' : v.new_str;
    return (tree) => {
      if (!isSafe(p)) throw new EditFail('unsafe', p);
      const before = tree.read(p);
      if (before === null) throw new EditFail('missing', p);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const norm = (s) => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = norm(before);
      const old = norm(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new EditFail('no-match', p);
      if (count > 1) throw new EditFail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + norm(newStr) + t.slice(at + old.length);
      tree.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (v.command === 'insert') {
    if (typeof v.insert_line !== 'number' || !Number.isInteger(v.insert_line)) return null;
    if (typeof v.new_str !== 'string') return null;
    const line = v.insert_line;
    const add = splitPatch(v.new_str);
    return (tree) => {
      if (!isSafe(p)) throw new EditFail('unsafe', p);
      const before = tree.read(p);
      if (before === null) throw new EditFail('missing', p);
      const f = parseText(before);
      if (line < 0 || line > f.lines.length) throw new EditFail('no-match', p);
      const lines = f.lines.slice(0, line).concat(add, f.lines.slice(line));
      tree.set(p, renderText({ br: f.br, lines, fin: f.fin }));
    };
  }
  return null;
}

function parseJson(text, lines) {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new ParseErr(1);
  const edits = [];
  if (lines[first].trimStart().startsWith('[')) {
    let v;
    try {
      v = JSON.parse(text);
    } catch {
      throw new ParseErr(first + 1);
    }
    if (!Array.isArray(v)) throw new ParseErr(first + 1);
    for (const x of v) {
      const e = makeJsonEdit(x);
      if (e === null) throw new ParseErr(first + 1);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e = null;
    try {
      e = makeJsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new ParseErr(i + 1);
    edits.push(e);
  });
  return edits;
}

// ---- format detection (SPEC.md section 4) ----

function detect(lines) {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first].trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first].trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && i + 1 < lines.length && lines[i + 1].startsWith('+++ ')))) return 'unified';
  return null;
}

function parsePatch(kind, lines, text, strict) {
  if (kind === 'unified') return parseUnified(lines, strict);
  if (kind === 'search-replace') return parseSearchReplace(lines, strict);
  if (kind === 'v4a') return parseV4A(lines, strict);
  return parseJson(text, lines);
}

// ---- output: what changed, and writing it ----

function changeRows(tree, moves) {
  const rows = [];
  const covered = new Set();
  for (const [oldP, newP] of moves) {
    const oOld = tree.orig(oldP);
    const oNew = tree.orig(newP);
    const cOld = tree.read(oldP);
    const cNew = tree.read(newP);
    if (oOld !== null && cOld === null && oNew === null && cNew !== null) {
      rows.push({ key: newP, text: `R ${oldP} -> ${newP}` });
      covered.add(oldP);
      covered.add(newP);
    }
  }
  for (const p of tree.cur.keys()) {
    if (covered.has(p)) continue;
    const was = tree.orig(p);
    const now = tree.cur.get(p);
    if (was === now) continue;
    if (was === null) rows.push({ key: p, text: `A ${p}` });
    else if (now === null) rows.push({ key: p, text: `D ${p}` });
    else rows.push({ key: p, text: `M ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key, 'utf8'), Buffer.from(b.key, 'utf8')));
  return rows;
}

function writeTree(tree) {
  const paths = [...tree.cur.keys()].sort((a, b) => Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8')));
  for (const p of paths) {
    const was = tree.orig(p);
    const now = tree.cur.get(p);
    if (was === now) continue;
    if (now === null) {
      rmSync(p, { force: true });
    } else {
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
  }
}

// ---- command line (SPEC.md sections 1, 2 and 10) ----

function run(argv) {
  let format = null;
  let check = false;
  let strict = false;
  const pos = [];
  let ended = false;
  for (const a of argv) {
    if (!ended && a === '--') { ended = true; continue; }
    if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=')) {
        if (format !== null) return { code: 2, out: ['error: usage'] };
        const v = a.slice(9);
        if (!FORMATS.includes(v)) return { code: 2, out: ['error: usage'] };
        format = v;
      } else if (a === '--check') {
        if (check) return { code: 2, out: ['error: usage'] };
        check = true;
      } else if (a === '--strict') {
        if (strict) return { code: 2, out: ['error: usage'] };
        strict = true;
      } else {
        return { code: 2, out: ['error: usage'] };
      }
    } else {
      pos.push(a);
    }
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const patchFile = pos.length === 0 || pos[0] === '-' ? null : pos[0];
  let text = '';
  try {
    text = readFileSync(patchFile === null ? 0 : patchFile, 'utf8');
  } catch {
    if (patchFile !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = splitPatch(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits;
  try {
    edits = parsePatch(kind, lines, text, strict);
  } catch (e) {
    if (e instanceof ParseErr) return { code: 2, out: [`error: parse ${e.line}`] };
    throw e;
  }
  if (edits.length === 0) return { code: 2, out: ['error: parse 1'] };
  const tree = new Tree();
  const moves = [];
  const fails = [];
  for (const edit of edits) {
    const snap = new Map(tree.cur);
    try {
      edit(tree, moves);
    } catch (e) {
      if (!(e instanceof EditFail)) throw e;
      tree.cur = snap;
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    const out = fails.map((f) => `error: ${f.code} ${f.path}`);
    out.push(`failed: ${fails.length} of ${edits.length} edits`);
    return { code: 1, out };
  }
  const rows = changeRows(tree, moves);
  if (!check) writeTree(tree);
  const out = rows.map((r) => r.text);
  out.push(`ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`);
  return { code: 0, out };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this
  // file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
