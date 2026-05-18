'use strict';
// Per-language extractors that pull the user-relevant slice out of an
// emitted JS file, hiding the runtime/stdlib so docs focus on what the
// verified program actually compiles to.
//
// Each extractor returns:
//   string  — the slice to show in docs
//   ''      — file is pure runtime/stdlib, elide entirely
//   null    — no special extraction, show the file as-is

// --- Brace-matching helpers ------------------------------------------------

// Given a substring index pointing at (or before) a `{`, return the index
// just past the matching `}` at depth 0, skipping JS string and comment
// content.
function matchBraceFrom(content, fromIndex) {
  let i = content.indexOf('{', fromIndex);
  if (i < 0) return -1;
  let depth = 1;
  i++;
  while (i < content.length && depth > 0) {
    const c = content[i];
    const n = content[i + 1];
    if (c === '"' || c === "'" || c === '`') {
      const q = c;
      i++;
      while (i < content.length && content[i] !== q) {
        if (content[i] === '\\') i++;
        i++;
      }
      i++;
    } else if (c === '/' && n === '/') {
      while (i < content.length && content[i] !== '\n') i++;
    } else if (c === '/' && n === '*') {
      i += 2;
      while (i < content.length - 1 && !(content[i] === '*' && content[i + 1] === '/')) i++;
      i += 2;
    } else if (c === '{') { depth++; i++; }
    else if (c === '}')   { depth--; i++; }
    else i++;
  }
  return i;
}

// --- Dafny -----------------------------------------------------------------

// Dafny output is a single file. We keep:
//   - the user's `let <ModuleName> = (function() { ... })()` block
//   - the trailing Main invocation line (so readers see how it's launched)
// and drop the ~600-line _dafny runtime prelude and the _System / _module
// scaffolding.
function extractDafny(content, moduleName) {
  const startRe = new RegExp(`^let ${moduleName} = \\(function\\(\\)`, 'm');
  const m = content.match(startRe);
  if (!m) return null;
  const endMarker = `// end of module ${moduleName}`;
  const endIdx = content.indexOf(endMarker, m.index);
  const endOfLine = endIdx >= 0 ? content.indexOf('\n', endIdx) : -1;
  const userBlock = content.slice(m.index, endOfLine > 0 ? endOfLine : content.length);
  // Tail: the launcher line (HandleHaltExceptions(...)).
  const launcher = content.match(/_dafny\.HandleHaltExceptions[^\n]*/);
  const out = launcher ? `${userBlock}\n\n// ... runtime prelude elided ...\n\n${launcher[0]}` : userBlock;
  return out;
}

// --- Agda ------------------------------------------------------------------

// Agda emits one JS file per Agda module. Stdlib modules (`jAgda.Agda.*`)
// are pure runtime; we elide them entirely. The user module is small
// enough to show in full; we strip the trailing main side-effect line.
function extractAgda(relPath, content) {
  if (relPath === 'agda-rts.js') return '';
  if (/^jAgda\.Agda\./.test(relPath)) return '';
  return content.replace(/\nexports\["main"\]\(a => \(\{\}\)\)\s*$/, '');
}

// --- Idris2 ----------------------------------------------------------------

// Idris2's --cg node output is a single executable with ~50 lines of
// `__prim_*`, `__lazy`, `__tailRec` helpers at the top, then the user
// functions (always prefixed with `<ModuleName>_`), then a try/catch that
// invokes main. We extract the user functions plus the launcher line.
function extractIdris2(content, moduleName) {
  const startRe = new RegExp(`^function ${moduleName}_[A-Za-z0-9_$]+`, 'gm');
  const positions = [];
  let m;
  while ((m = startRe.exec(content))) positions.push(m.index);
  if (positions.length === 0) return null;
  const blocks = positions.map((start) => {
    const end = matchBraceFrom(content, start);
    return content.slice(start, end);
  });
  const launcher = content.match(/__mainExpression_0\s*=[^\n]*/);
  const launcherLine = launcher ? `\nconst ${launcher[0]}` : '';
  const trailer = content.match(/try\{__mainExpression_0\(\)[^\n]*/);
  return blocks.join('\n\n') +
    (launcherLine ? `\n\n// ... runtime helpers elided ...\n${launcherLine}` : '') +
    (trailer ? `\n${trailer[0]}` : '');
}

module.exports = { extractDafny, extractAgda, extractIdris2 };
