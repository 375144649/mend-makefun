// mend applies text edits as specified in SPEC.md. Run it with Node 22.

import { lstatSync, mkdirSync, readdirSync, readFileSync, rmdirSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname, join } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function parseError(line: number): never {
  throw new Exit2(`error: parse ${line}`);
}

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: { from: string; to: string }[] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
  move(from: string, to: string, text: string): void {
    this.now.set(from, null);
    this.now.set(to, text);
    this.moves.push({ from, to });
  }
}

type Edit = (tree: Tree, strict: boolean) => void;

function checkPaths(...paths: (string | null)[]): void {
  for (const path of paths) {
    if (path !== null && !safe(path)) throw new Fail('unsafe', path);
  }
}

function existingFile(tree: Tree, path: string): string {
  const text = tree.get(path);
  if (text === null) throw new Fail('missing', path);
  return text;
}

function vacantPath(tree: Tree, path: string): void {
  if (tree.get(path) !== null) throw new Fail('exists', path);
}

function lineBreak(text: string): string {
  const firstLF = text.indexOf('\n');
  return firstLF > 0 && text[firstLF - 1] === '\r' ? '\r\n' : '\n';
}

function splitFile(text: string): { lines: string[]; br: string; final: boolean } {
  const br = lineBreak(text);
  const lines = text === '' ? [] : text.split(br);
  const final = text.endsWith(br);
  if (final) lines.pop();
  return { lines, br, final };
}

function joinFile(lines: string[], br: string, final: boolean): string {
  return lines.length === 0 ? '' : lines.join(br) + (final ? br : '');
}

function replaceLines(lines: string[], at: number, count: number, newLines: string[]): string[] {
  return lines.slice(0, at).concat(newLines, lines.slice(at + count));
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

const trimTrailing = (line: string): string => line.replace(/[ \t]+$/, '');
const trimBoth = (line: string): string => trimTrailing(line).replace(/^[ \t]+/, '');
const lineTiers = [(line: string): string => line, trimTrailing, trimBoth];

function findLines(
  lines: string[], old: string[], strict: boolean, first = 0, last = lines.length - old.length,
): { tier: number; positions: number[] } | null {
  if (first > last) return null;
  for (let tier = 0; tier < (strict ? 1 : lineTiers.length); tier++) {
    const normalize = lineTiers[tier]!;
    const needle = old.map(normalize);
    const haystack = tier === 0 ? lines : lines.map(normalize);
    const positions: number[] = [];
    for (let at = first; at <= last; at++) {
      if (needle.every((line, offset) => haystack[at + offset] === line)) positions.push(at);
    }
    if (positions.length > 0) return { tier, positions };
  }
  return null;
}

type WrittenLine = { text: string; context: number | null; noFinalBreak: boolean };
type LineChange = { old: string[]; written: WrittenLine[] };

function readChange(body: string[]): LineChange {
  const old: string[] = [];
  const written: WrittenLine[] = [];
  body.forEach((line, i) => {
    const prefix = line[0] ?? ' ';
    if (prefix === '\\') return;
    const text = line.slice(1);
    const context = prefix === ' ' ? old.length : null;
    if (prefix !== '+') old.push(text);
    if (prefix !== '-') {
      written.push({ text, context, noFinalBreak: body[i + 1]?.startsWith('\\') ?? false });
    }
  });
  return { old, written };
}

function replacement(change: LineChange, lines: string[], at: number, tier: number): string[] {
  const patchIndent = tier === 2 ? change.old[0]!.match(/^[ \t]*/)![0] : '';
  const fileIndent = tier === 2 ? lines[at]!.match(/^[ \t]*/)![0] : '';
  return change.written.map(({ text, context }) => {
    if (context !== null) return lines[at + context]!;
    if (tier === 2 && !blank(text) && text.startsWith(patchIndent)) {
      return fileIndent + text.slice(patchIndent.length);
    }
    return text;
  });
}

function searchReplaceEdits(lines: string[]): Edit[] {
  const markers = lines.map((line) => line.trimEnd());
  const edits: Edit[] = [];
  let previousPath: string | undefined;
  let outsideStart = 0;
  for (let i = 0; i < lines.length; i++) {
    if (markers[i] !== '<<<<<<< SEARCH') continue;
    const search = i;
    let path = previousPath;
    for (let p = search - 1; p >= outsideStart; p--) {
      const candidate = lines[p]!.trim();
      if (candidate === '' || candidate.startsWith('```')) continue;
      path = candidate;
      break;
    }
    if (path === undefined) parseError(search + 1);
    const target = path;
    const separator = markers.indexOf('=======', search + 1);
    const end = separator < 0 ? -1 : markers.indexOf('>>>>>>> REPLACE', separator + 1);
    if (end < 0) parseError(search + 1);
    const old = lines.slice(search + 1, separator);
    const added = lines.slice(separator + 1, end);
    const change: LineChange = {
      old,
      written: added.map((text) => ({ text, context: null, noFinalBreak: false })),
    };
    edits.push((tree, strict) => {
      checkPaths(target);
      if (old.length === 0) {
        vacantPath(tree, target);
        tree.now.set(target, joinFile(added, '\n', true));
        return;
      }
      const { lines: current, br, final } = splitFile(existingFile(tree, target));
      const match = findLines(current, old, strict);
      if (match === null) throw new Fail('no-match', target);
      if (match.positions.length > 1) throw new Fail('ambiguous', target);
      const at = match.positions[0]!;
      const next = replaceLines(current, at, old.length, replacement(change, current, at, match.tier));
      tree.now.set(target, joinFile(next, br, final));
    });
    previousPath = target;
    i = end;
    outsideStart = end + 1;
  }
  return edits;
}

type UnifiedHunk = LineChange & { start: number };
type UnifiedSection = {
  gitPaths?: [string, string];
  headerPaths?: [string | null, string | null];
  renameFrom?: string;
  renameTo?: string;
  create?: boolean;
  delete?: boolean;
  hunks: UnifiedHunk[];
};

function headerPath(line: string): string | null {
  const path = line.slice(4).split('\t', 1)[0]!.trim();
  return path === '/dev/null' ? null : path.replace(/^[ab]\//, '');
}

function unifiedEdit(section: UnifiedSection): Edit {
  const [from, to] = section.headerPaths
    ?? [section.renameFrom ?? section.gitPaths![0], section.renameTo ?? section.gitPaths![1]];
  return (tree, strict) => {
    checkPaths(from, to);
    if (from === null || section.create) {
      const target = to ?? '';
      checkPaths(target);
      vacantPath(tree, target);
      const added = section.hunks.flatMap((hunk) => hunk.written.filter((line) => line.context === null));
      tree.now.set(target, joinFile(added.map((line) => line.text), '\n', !added.at(-1)?.noFinalBreak));
      return;
    }
    const original = existingFile(tree, from);
    if (to === null || section.delete) {
      tree.now.set(from, null);
      return;
    }
    if (to !== from) vacantPath(tree, to);
    let { lines, br, final } = splitFile(original);
    let delta = 0;
    for (const hunk of section.hunks) {
      let at: number;
      let tier = 0;
      if (hunk.old.length === 0) {
        at = Math.max(0, Math.min(lines.length, hunk.start + delta));
      } else {
        const match = findLines(lines, hunk.old, strict);
        if (match === null) throw new Fail('no-match', from);
        tier = match.tier;
        const target = Math.max(0, Math.min(lines.length, hunk.start - 1 + delta));
        at = match.positions[0]!;
        for (const position of match.positions) {
          if (Math.abs(position - target) < Math.abs(at - target)) at = position;
        }
      }
      if (at + hunk.old.length === lines.length) final = !hunk.written.at(-1)?.noFinalBreak;
      lines = replaceLines(lines, at, hunk.old.length, replacement(hunk, lines, at, tier));
      delta += hunk.written.length - hunk.old.length;
    }
    const result = joinFile(lines, br, final);
    if (to !== from) tree.move(from, to, result);
    else tree.now.set(from, result);
  };
}

function unifiedEdits(lines: string[]): Edit[] {
  const sections: UnifiedSection[] = [];
  const gitHeader = (line: string): boolean => line === 'diff --git' || line.startsWith('diff --git ');
  const pathPair = (at: number): boolean => lines[at]!.startsWith('--- ') && (lines[at + 1]?.startsWith('+++ ') ?? false);
  let section: UnifiedSection | undefined;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]!;
    if (gitHeader(line)) {
      const match = /^diff --git a\/(.+?) b\/(.+)$/s.exec(line);
      if (match === null) parseError(i + 1);
      section = { gitPaths: [match[1]!, match[2]!], hunks: [] };
      sections.push(section);
    } else if (pathPair(i)) {
      if (section === undefined || section.headerPaths !== undefined || section.hunks.length !== 0) {
        section = { hunks: [] };
        sections.push(section);
      }
      section.headerPaths = [headerPath(line), headerPath(lines[++i]!)];
    } else if (line.startsWith('@@')) {
      const match = /^@@ -(\d+)(?:,\d+)? \+\d+(?:,\d+)? @@/.exec(line);
      if (match === null || section === undefined) parseError(i + 1);
      const start = Number(match[1]);
      const bodyStart = i + 1;
      while (i + 1 < lines.length) {
        const next = lines[i + 1]!;
        if (gitHeader(next) || pathPair(i + 1) || (next !== '' && !' +-\\'.includes(next[0]!))) break;
        i++;
      }
      const body = lines.slice(bodyStart, i + 1);
      while (body.at(-1) === '') body.pop();
      section.hunks.push({ start, ...readChange(body) });
    } else if (section !== undefined && section.hunks.length === 0) {
      if (line.startsWith('--- ')) parseError(i + 2);
      if (line.startsWith('rename from ')) section.renameFrom = line.slice(12);
      else if (line.startsWith('rename to ')) section.renameTo = line.slice(10);
      else if (/^new file mode(?: |$)/.test(line)) section.create = true;
      else if (/^deleted file mode(?: |$)/.test(line)) section.delete = true;
    }
  }
  return sections.map(unifiedEdit);
}

type V4AChunk = LineChange & { anchor: string; eof: boolean };

function v4aUpdate(lines: string[], first: number, end: number, path: string): Edit {
  let i = first;
  let destination: string | undefined;
  if (i < end && lines[i]!.startsWith('*** Move to: ')) destination = lines[i++]!.slice(13).trim();
  const chunks: V4AChunk[] = [];
  while (i < end) {
    let anchor = '';
    const header = lines[i]!.startsWith('@@');
    if (header) anchor = lines[i++]!.slice(2).trim();
    const start = i;
    while (i < end && (lines[i] === '' || ' +-'.includes(lines[i]![0]!))) i++;
    if (!header && (chunks.length > 0 || start === i)) parseError(start + 1);
    const body = lines.slice(start, i);
    const eof = i < end && lines[i] === '*** End of File';
    if (eof) i++;
    chunks.push({ ...readChange(body), anchor, eof });
  }
  if (chunks.length === 0 && destination === undefined) parseError(first);
  return (tree, strict) => {
    checkPaths(path, destination ?? null);
    const original = existingFile(tree, path);
    if (destination !== undefined) vacantPath(tree, destination);
    let { lines: current, br, final } = splitFile(original);
    let cursor = 0;
    for (const chunk of chunks) {
      if (chunk.anchor !== '') {
        const match = findLines(current, [chunk.anchor], strict, cursor);
        if (match === null) throw new Fail('no-match', path);
        cursor = match.positions[0]! + 1;
      }
      let at = chunk.eof ? current.length : cursor;
      let tier = 0;
      if (chunk.old.length !== 0) {
        const last = current.length - chunk.old.length;
        const first = chunk.eof ? Math.max(cursor, last) : cursor;
        const match = findLines(current, chunk.old, strict, first, last);
        if (match === null) throw new Fail('no-match', path);
        at = match.positions[0]!;
        tier = match.tier;
      }
      current = replaceLines(current, at, chunk.old.length, replacement(chunk, current, at, tier));
      cursor = at + chunk.written.length;
    }
    const result = joinFile(current, br, final);
    if (destination === undefined) tree.now.set(path, result);
    else tree.move(path, destination, result);
  };
}

function v4aEdits(lines: string[]): Edit[] {
  const first = lines.findIndex((line) => !blank(line));
  if (first < 0 || lines[first]!.trim() !== '*** Begin Patch') parseError(first < 0 ? 1 : first + 1);
  const last = lines.findLastIndex((line) => !blank(line));
  if (last === first || lines[last]!.trim() !== '*** End Patch') parseError(lines.length + 1);
  const sectionHeader = /^\*\*\* (Add|Delete|Update) File: (.*)$/s;
  const edits: Edit[] = [];
  for (let i = first + 1; i < last;) {
    if (blank(lines[i]!)) {
      i++;
      continue;
    }
    const header = sectionHeader.exec(lines[i]!);
    if (header === null) parseError(i + 1);
    const kind = header[1];
    const path = header[2]!.trim();
    const start = ++i;
    while (i < last && !sectionHeader.test(lines[i]!)) i++;
    let end = i;
    while (end > start && blank(lines[end - 1]!)) end--;
    if (kind === 'Add') {
      const added = lines.slice(start, end).map((line, offset) => {
        if (line !== '' && !line.startsWith('+')) parseError(start + offset + 1);
        return line.slice(1);
      });
      edits.push((tree) => {
        checkPaths(path);
        vacantPath(tree, path);
        tree.now.set(path, joinFile(added, '\n', true));
      });
    } else if (kind === 'Delete') {
      if (start !== end) parseError(start + 1);
      edits.push((tree) => {
        checkPaths(path);
        existingFile(tree, path);
        tree.now.set(path, null);
      });
    } else {
      edits.push(v4aUpdate(lines, start, end, path));
    }
  }
  return edits;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    checkPaths(p);
    return existingFile(tree, p);
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      checkPaths(p);
      vacantPath(tree, p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const crlf = lineBreak(before) === '\r\n';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      const at = t.indexOf(old);
      if (at < 0) throw new Fail('no-match', p);
      if (t.indexOf(old, at + 1) >= 0) throw new Fail('ambiguous', p);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const { lines, br, final } = splitFile(exists(tree));
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      tree.now.set(p, joinFile(replaceLines(lines, line, 0, add), br, final));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) parseError(1);
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      parseError(first + 1);
    }
    if (!Array.isArray(v)) parseError(first + 1);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) parseError(first + 1);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) parseError(i + 1);
    edits.push(e);
  });
  return edits;
}

function removeEmptyDirectory(path: string): void {
  if (!lstatSync(path, { throwIfNoEntry: false })?.isDirectory()) return;
  for (const entry of readdirSync(path, { withFileTypes: true })) {
    if (entry.isDirectory()) removeEmptyDirectory(join(path, entry.name));
  }
  rmdirSync(path);
}

function writeChanges(tree: Tree): void {
  // A removed file can make way for a directory, or vice versa.
  for (const [path, now] of tree.now) {
    if (now === null && tree.original(path) !== null) rmSync(path, { force: true });
  }
  for (const [path, now] of tree.now) {
    if (now !== null && now !== tree.original(path)) {
      mkdirSync(dirname(path), { recursive: true });
      removeEmptyDirectory(path);
      writeFileSync(path, now);
    }
  }
}

function summarize(tree: Tree): string[] {
  const changed = new Map<string, string>();
  for (const [path, now] of tree.now) {
    const before = tree.original(path);
    if (now !== before) changed.set(path, before === null ? 'A' : now === null ? 'D' : 'M');
  }
  const moves = new Map<string, string>();
  for (const { from, to } of tree.moves) {
    if (changed.get(from) === 'D' && changed.get(to) === 'A') {
      changed.delete(from);
      changed.delete(to);
      moves.set(to, from);
    }
  }
  const paths = [...changed.keys(), ...moves.keys()];
  paths.sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)));
  return paths.map((path) => {
    const from = moves.get(path);
    return from === undefined ? `${changed.get(path)} ${path}` : `R ${from} -> ${path}`;
  });
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    switch (kind) {
      case 'json':
        edits = jsonEdits(text, lines);
        break;
      case 'search-replace':
        edits = searchReplaceEdits(lines);
        break;
      case 'unified':
        edits = unifiedEdits(lines);
        break;
      default:
        edits = v4aEdits(lines);
    }
    if (edits.length === 0) parseError(1);
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    try {
      edit(tree, strict);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const rows = summarize(tree);
  if (!check) writeChanges(tree);
  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}


const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
