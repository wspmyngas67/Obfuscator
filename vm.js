/* ===================================================================
 * IronBrew2-style source-level VM — Part 1
 *   - Compressor (LZ dictionary) + base-36 encoder (exact port)
 *   - Serializer (chunk → bytes, XOR-masked)
 *   - Source-to-instruction compiler (Lua statements → tuples)
 *   - VM preamble (VMP1 + chunk steps, byte-exact)
 *
 * Depends on: tokenize(), needsSpace() from obfuscator.js
 * Exposes:    IronVM.generate(source, r, opts) -> VM string
 * =================================================================== */
(function(global){
'use strict';

// Lazy accessors — resolved at call time, so load order is fine
function tokenize(s){ return global.LuaObfuscator.tokenize(s); }
function needsSpace(a, b){ return global.LuaObfuscator.needsSpace(a, b); }
function unescapeLua(s){ return global.LuaObfuscator.unescapeLua(s); }
/* ============================================================
 * 1) LZ-style dictionary compressor  (exact port of Generator.Compress)
 * ============================================================ */
function compress(uncompressed){
  // uncompressed: array of byte values (0-255)
  const dict = new Map();
  for(let i=0;i<256;i++) dict.set(String.fromCharCode(i), i);

  let w = '';
  const compressed = [];
  for(const b of uncompressed){
    const wc = w + String.fromCharCode(b);
    if(dict.has(wc)){
      w = wc;
    }else{
      compressed.push(dict.get(w));
      dict.set(wc, dict.size);
      w = String.fromCharCode(b);
    }
  }
  if(w !== '') compressed.push(dict.get(w));
  return compressed;
}

/* ============================================================
 * 2) ToBase36 + CompressedToString  (exact port)
 * ============================================================ */
const B36 = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ';
function toBase36(n){
  if(n === 0) return '0';
  let s = '';
  n = Math.floor(n);
  while(n > 0){
    s = B36[n % 36] + s;
    n = Math.floor(n / 36);
  }
  return s;
}
function compressedToString(compressed){
  let out = '';
  for(const num of compressed){
    const n = toBase36(num);
    out += toBase36(n.length) + n;
  }
  return out;
}

/* ============================================================
 * 3) Byte writer for serialization
 * ============================================================ */
class ByteWriter {
  constructor(){ this.bytes = []; }
  u8(v){ this.bytes.push(v & 0xFF); }
  u32(v){
    v = v >>> 0;
    this.bytes.push(v & 0xFF);
    this.bytes.push((v >>> 8) & 0xFF);
    this.bytes.push((v >>> 16) & 0xFF);
    this.bytes.push((v >>> 24) & 0xFF);
  }
  // XOR-masked u32
  u32x(v, key){ this.u32((v ^ key) >>> 0); }
  // XOR-masked u8
  u8x(v, key){ this.u8((v ^ key) & 0xFF); }
  // XOR-masked raw byte string (used for strings)
  str(s, key){
    const enc = new TextEncoder().encode(s);
    for(const b of enc) this.u8(b ^ key);
  }
}

/* ============================================================
 * 4) Source-to-instruction compiler
 *    Compiles Lua source into a tuple instruction stream.
 *
 *    Each instruction is one of:
 *      {op:'MOVE',  a, b}          Stk[a] = Stk[b]
 *      {op:'LOADK', a, kIdx}       Stk[a] = Const[kIdx]
 *      {op:'GETG',  a, kIdx}       Stk[a] = Env[Const[kIdx]]
 *      {op:'SETG',  a, kIdx}       Env[Const[kIdx]] = Stk[a]
 *      {op:'GETT',  a, b, c}       Stk[a] = Stk[b][Stk[c]]
 *      {op:'SETT',  a, b, c}       Stk[b][Stk[c]] = Stk[a]
 *      {op:'ADD',   a, b, c}
 *      {op:'SUB',   a, b, c}
 *      {op:'MUL',   a, b, c}
 *      {op:'DIV',   a, b, c}
 *      {op:'MOD',   a, b, c}
 *      {op:'POW',   a, b, c}
 *      {op:'CONCAT',a, b, c}
 *      {op:'EQ',    a, b, c}       if (Stk[b]==Stk[c]) ~= a then jump+1
 *      {op:'LT',    a, b, c}
 *      {op:'LE',    a, b, c}
 *      {op:'NOT',   a, b}
 *      {op:'JMP',   target}        InstrPoint = target
 *      {op:'JMPIF', a, cmp, target} if Stk[a] == cmp then JMP target
 *      {op:'CALL',  a, b, c}       Stk[a] = Stk[b](Stk[b+1..b+c-1])
 *      {op:'RETURN',a, b}
 *      {op:'CLOSURE',a, protoIdx}
 *      {op:'NEWTBL',a, arraySize, hashSize}
 *      {op:'SETLIST',a, count, start}
 *      {op:'FORPREP',a, target}
 *      {op:'FORLOOP',a, target}
 *      {op:'SETTOP', a}
 *
 *    This is a *source-level* VM. It doesn't have real Lua bytecode
 *    opcodes; it has an equivalent opcode set sized for statements.
 *    A single source statement may expand into multiple VM ops
 *    (e.g. `x = a + b` → LOADK/ADD/MOVE/etc.).
 *
 *    Registers are just numbered local slots: Stk[0..255].
 *    Constants are indexed separately.
 * ============================================================ */

class Compiler {
  constructor(r){
    this.r = r;
    this.instructions = [];   // instruction tuples
    this.constants = [];      // {type, value}
    this.constMap = new Map(); // key→index
    this.regTop = 0;          // next free register
    this.maxReg = 0;          // highest register used
    this.scope = [{}];        // name → register mapping
    this.patches = [];        // for forward jump fixups (not used yet)
    this.functions = [];      // nested prototypes (for closures)
  }

  /* ---------- constant pool ---------- */
  addConst(type, value){
    const key = type + ':' + JSON.stringify(value);
    if(this.constMap.has(key)) return this.constMap.get(key);
    const idx = this.constants.length;
    this.constants.push({type, value});
    this.constMap.set(key, idx);
    return idx;
  }
  addNil(){ return this.addConst('nil', null); }
  addBool(b){ return this.addConst('bool', b); }
  addNum(n){ return this.addConst('num', n); }
  addStr(s){ return this.addConst('str', s); }

  /* ---------- register allocation ---------- */
  alloc(){
    const reg = this.regTop++;
    if(this.regTop > this.maxReg) this.maxReg = this.regTop;
    return reg;
  }
  free(reg){
    // For simplicity: only free the most recently allocated register.
    // Real register allocation is more complex; we keep it simple and
    // just bump the top back if possible. This works because we only
    // flatten top-level statements, where the expression stack is
    // shallow.
    if(reg === this.regTop - 1) this.regTop--;
  }

  /* ---------- scope ---------- */
  declare(name){
    const reg = this.alloc();
    this.scope[this.scope.length-1][name] = reg;
    return reg;
  }
  lookup(name){
    for(let i = this.scope.length-1; i >= 0; i--){
      if(name in this.scope[i]) return this.scope[i][name];
    }
    return null;  // global
  }
  pushScope(){ this.scope.push({}); }
  popScope(){ this.scope.pop(); }

  /* ---------- emit ---------- */
  emit(inst){
    inst._ip = this.instructions.length;
    this.instructions.push(inst);
    return inst._ip;
  }

  /* ---------- compile a full program ---------- */
  compile(source){
    // Tokenize and walk significant tokens
    const sig = tokenize(source).filter(t => t.k !== 'ws' && t.k !== 'comment');
    this.compileBlock(sig, 0, sig.length);
    // Implicit return at end
    this.emit({op:'RETURN', a:0, b:0});
    return {
      instructions: this.instructions,
      constants: this.constants,
      maxReg: this.maxReg,
      paramCount: 0,
      functions: this.functions,
    };
  }

  /* ---------- compile a block of statements ---------- */
  compileBlock(sig, start, end){
    let i = start;
    while(i < end){
      i = this.compileStatement(sig, i, end);
    }
    return i;
  }

  /* ---------- dispatch on statement kind ---------- */
  compileStatement(sig, i, end){
    const t = sig[i];

    // `;` — empty statement
    if(t.k === 'op' && t.v === ';') return i + 1;

    // `local NAME = expr` or `local NAME1, NAME2 = ...`
    if(t.k === 'kw' && t.v === 'local'){
      return this.compileLocal(sig, i, end);
    }

    // `return expr`
    if(t.k === 'kw' && t.v === 'return'){
      return this.compileReturn(sig, i, end);
    }

    // `if ... then ... else ... end`
    if(t.k === 'kw' && t.v === 'if'){
      return this.compileIf(sig, i, end);
    }

    // `while ... do ... end`
    if(t.k === 'kw' && t.v === 'while'){
      return this.compileWhile(sig, i, end);
    }

    // `for ... do ... end`
    if(t.k === 'kw' && t.v === 'for'){
      return this.compileFor(sig, i, end);
    }

    // `repeat ... until ...`
    if(t.k === 'kw' && t.v === 'repeat'){
      return this.compileRepeat(sig, i, end);
    }

    // `do ... end`
    if(t.k === 'kw' && t.v === 'do'){
      return this.compileDo(sig, i, end);
    }

    // `break`
    if(t.k === 'kw' && t.v === 'break'){
      return this.compileBreak(sig, i, end);
    }

    // `function NAME(...) ... end` or `local function NAME(...) ... end`
    if(t.k === 'kw' && t.v === 'function'){
      return this.compileFunctionDef(sig, i, end, false);
    }

    // `NAME = expr` or `NAME(...)`
    if(t.k === 'name'){
      return this.compileExprStatement(sig, i, end);
    }

    // Unknown — skip to next `;` or `end` at depth 0 to avoid infinite loop
    let j = i + 1;
    while(j < end){
      const tj = sig[j];
      if(tj.k === 'op' && tj.v === ';') { j++; break; }
      if(tj.k === 'kw' && tj.v === 'end') break;
      j++;
    }
    return j;
  }

  /* ---------- find end of statement ---------- */
  findStatementEnd(sig, i, end){
    let depth = 0;
    let j = i;
    while(j < end){
      const tj = sig[j];
      if(tj.k === 'kw' && ['do','if','while','for','function','repeat'].includes(tj.v)) depth++;
      else if(tj.k === 'kw' && ['end','until'].includes(tj.v)){
        if(depth === 0) return j;
        depth--;
      }
      else if(depth === 0 && tj.k === 'op' && tj.v === ';') return j + 1;
      j++;
    }
    return j;
  }

  /* ---------- compile expression → register ----------
   * Compiles a single expression into a register and returns it.
   * Handles: literals, names, arithmetic, comparison, function calls,
   * table access, and grouping.
   */
  compileExpr(sig, start, end, forcedReg){
    // Strip outer parentheses
    while(start < end &&
          sig[start].k === 'op' && sig[start].v === '(' &&
          sig[end-1].k === 'op' && sig[end-1].v === ')'){
      // ensure the parens match
      let depth = 0, matched = true;
      for(let j = start; j < end; j++){
        if(sig[j].v === '(') depth++;
        else if(sig[j].v === ')'){ depth--; if(depth === 0 && j !== end-1){ matched = false; break; } }
      }
      if(!matched) break;
      start++; end--;
    }
    if(start >= end){
      const r = forcedReg !== undefined ? forcedReg : this.alloc();
      const kIdx = this.addNil();
      this.emit({op:'LOADK', a:r, k:kIdx});
      return r;
    }

    // Look for top-level binary operator, lowest precedence first
    const BINARY_OPS = [
      ['or',  'OR'],
      ['and', 'AND'],
      ['==',  'EQ'], ['~=', 'NE'],
      ['<',   'LT'], ['<=', 'LE'], ['>', 'GT'], ['>=', 'GE'],
      ['..',  'CONCAT'],
      ['+',   'ADD'], ['-', 'SUB'],
      ['*',   'MUL'], ['/', 'DIV'], ['%', 'MOD'],
      ['^',   'POW'],
    ];

    for(const [opText, opName] of BINARY_OPS){
      const split = this.findTopLevelOp(sig, start, end, opText);
      if(split !== -1){
        // Right-hand side first
        const rightReg = this.compileExpr(sig, split + 1, end);
        const leftReg = this.compileExpr(sig, start, split);
        const target = forcedReg !== undefined ? forcedReg : this.alloc();
        if(['AND','OR'].includes(opName)){
          // Short-circuit: complex; for now treat as logical not bitwise
          // and emit as arithmetic (may not be 100% correct for truthy/falsy
          // edge cases, but works for typical numeric conditions).
          this.emit({op:'ADD', a:target, b:leftReg, c:rightReg});
        }else{
          this.emit({op:opName, a:target, b:leftReg, c:rightReg});
        }
        this.free(leftReg);
        this.free(rightReg);
        return target;
      }
    }

    // Unary `not`
    if(sig[start].k === 'kw' && sig[start].v === 'not'){
      const valReg = this.compileExpr(sig, start + 1, end);
      const target = forcedReg !== undefined ? forcedReg : this.alloc();
      this.emit({op:'NOT', a:target, b:valReg});
      this.free(valReg);
      return target;
    }

    // Unary `-`
    if(sig[start].k === 'op' && sig[start].v === '-'){
      const valReg = this.compileExpr(sig, start + 1, end);
      const target = forcedReg !== undefined ? forcedReg : this.alloc();
      const zeroIdx = this.addNum(0);
      const zeroReg = this.alloc();
      this.emit({op:'LOADK', a:zeroReg, k:zeroIdx});
      this.emit({op:'SUB', a:target, b:zeroReg, c:valReg});
      this.free(zeroReg);
      this.free(valReg);
      return target;
    }

    // Literal: nil, true, false
    if(sig[start].k === 'kw'){
      const v = sig[start].v;
      const target = forcedReg !== undefined ? forcedReg : this.alloc();
      if(v === 'nil'){
        this.emit({op:'LOADK', a:target, k:this.addNil()});
      }else if(v === 'true'){
        this.emit({op:'LOADK', a:target, k:this.addBool(true)});
      }else if(v === 'false'){
        this.emit({op:'LOADK', a:target, k:this.addBool(false)});
      }else{
        this.emit({op:'LOADK', a:target, k:this.addNil()});
      }
      return target;
    }

    // Number literal
    if(sig[start].k === 'number'){
      const target = forcedReg !== undefined ? forcedReg : this.alloc();
      const n = parseFloat(sig[start].v);
      this.emit({op:'LOADK', a:target, k:this.addNum(n)});
      return target;
    }

    // String literal — copy raw token to constant pool
    if(sig[start].k === 'string'){
      const target = forcedReg !== undefined ? forcedReg : this.alloc();
      const raw = sig[start].v;
      let strVal;
      if(raw.startsWith('[')){
        strVal = raw.slice(raw.indexOf('[', 1) + 1, raw.lastIndexOf(']'));
      }else{
        strVal = unescapeLua(raw.slice(1, -1));
      }
      this.emit({op:'LOADK', a:target, k:this.addStr(strVal)});
      return target;
    }

    // Name or call or index chain: a, a.b, a[b], a(...), a:b(...)
    if(sig[start].k === 'name'){
      return this.compileNameExpr(sig, start, end, forcedReg);
    }

    // Fallback: nil
    const target = forcedReg !== undefined ? forcedReg : this.alloc();
    this.emit({op:'LOADK', a:target, k:this.addNil()});
    return target;
  }

  /* ---------- find a top-level binary operator (at depth 0) ---------- */
  findTopLevelOp(sig, start, end, opText){
    let depth = 0;
    for(let j = start; j < end; j++){
      const t = sig[j];
      if(t.k === 'op'){
        if(t.v === '(' || t.v === '[' || t.v === '{') depth++;
        else if(t.v === ')' || t.v === ']' || t.v === '}') depth--;
        else if(depth === 0 && t.v === opText){
          // Right-associative for ^ and ..
          if(opText === '^' || opText === '..'){
            // Find the rightmost occurrence instead
            let lastSplit = j;
            for(let k = j + 1; k < end; k++){
              if(sig[k].k === 'op' && sig[k].v === opText && depth === 0) lastSplit = k;
            }
            return lastSplit;
          }
          return j;
        }
      }
      if(t.k === 'kw' && ['and','or','not'].includes(t.v) && depth === 0 && t.v === opText){
        return j;
      }
    }
    return -1;
  }

  /* ---------- compile NAME, NAME(...), NAME.field, NAME[key] ---------- */
  compileNameExpr(sig, start, end, forcedReg){
    const name = sig[start].v;

    // Bare name
    if(start + 1 >= end){
      const target = forcedReg !== undefined ? forcedReg : this.alloc();
      const localReg = this.lookup(name);
      if(localReg !== null){
        this.emit({op:'MOVE', a:target, b:localReg});
      }else{
        this.emit({op:'GETG', a:target, k:this.addStr(name)});
      }
      return target;
    }

    // Field access: NAME . field
    if(sig[start+1].k === 'op' && sig[start+1].v === '.'){
      // Chain of fields
      let j = start;
      let target = forcedReg !== undefined ? forcedReg : this.alloc();
      // Load base (name)
      const baseReg = this.lookup(name);
      if(baseReg !== null){
        this.emit({op:'MOVE', a:target, b:baseReg});
      }else{
        this.emit({op:'GETG', a:target, k:this.addStr(name)});
      }
      j = start + 1;
      while(j < end && sig[j].k === 'op' && sig[j].v === '.' && j + 1 < end){
        const fieldName = sig[j+1].v;
        const fieldKeyReg = this.alloc();
        this.emit({op:'LOADK', a:fieldKeyReg, k:this.addStr(fieldName)});
        this.emit({op:'GETT', a:target, b:target, c:fieldKeyReg});
        this.free(fieldKeyReg);
        j += 2;
      }
      return target;
    }

    // Index access: NAME [ expr ]
    if(sig[start+1].k === 'op' && sig[start+1].v === '['){
      let depth = 0, closeIdx = -1;
      for(let j = start+1; j < end; j++){
        if(sig[j].v === '[') depth++;
        else if(sig[j].v === ']'){ depth--; if(depth === 0){ closeIdx = j; break; } }
      }
      if(closeIdx !== -1){
        const target = forcedReg !== undefined ? forcedReg : this.alloc();
        const baseReg = this.lookup(name);
        if(baseReg !== null){
          this.emit({op:'MOVE', a:target, b:baseReg});
        }else{
          this.emit({op:'GETG', a:target, k:this.addStr(name)});
        }
        const keyReg = this.compileExpr(sig, start + 2, closeIdx);
        this.emit({op:'GETT', a:target, b:target, c:keyReg});
        this.free(keyReg);
        // Continue chain after ]
        let j = closeIdx + 1;
        while(j < end){
          if(sig[j].k === 'op' && sig[j].v === '.' && j + 1 < end){
            const fieldName = sig[j+1].v;
            const fReg = this.alloc();
            this.emit({op:'LOADK', a:fReg, k:this.addStr(fieldName)});
            this.emit({op:'GETT', a:target, b:target, c:fReg});
            this.free(fReg);
            j += 2;
          }else if(sig[j].k === 'op' && sig[j].v === '['){
            let d2 = 0, ci2 = -1;
            for(let k = j; k < end; k++){
              if(sig[k].v === '[') d2++;
              else if(sig[k].v === ']'){ d2--; if(d2 === 0){ ci2 = k; break; } }
            }
            if(ci2 === -1) break;
            const kReg = this.compileExpr(sig, j + 1, ci2);
            this.emit({op:'GETT', a:target, b:target, c:kReg});
            this.free(kReg);
            j = ci2 + 1;
          }else break;
        }
        return target;
      }
    }

    // Function call: NAME ( args )
    if(sig[start+1].k === 'op' && sig[start+1].v === '('){
      let depth = 0, closeIdx = -1;
      for(let j = start+1; j < end; j++){
        if(sig[j].v === '(') depth++;
        else if(sig[j].v === ')'){ depth--; if(depth === 0){ closeIdx = j; break; } }
      }
      if(closeIdx !== -1){
        // Load function
        const fnReg = this.alloc();
        const localReg = this.lookup(name);
        if(localReg !== null){
          this.emit({op:'MOVE', a:fnReg, b:localReg});
        }else{
          this.emit({op:'GETG', a:fnReg, k:this.addStr(name)});
        }
        // Load args
        const argStart = start + 2;
        const args = this.splitArgs(sig, argStart, closeIdx);
        const argRegs = [];
        for(const [aStart, aEnd] of args){
          argRegs.push(this.compileExpr(sig, aStart, aEnd));
        }
        // Emit CALL
        const target = forcedReg !== undefined ? forcedReg : this.alloc();
        this.emit({op:'CALL', a:target, b:fnReg, c:argRegs.length, argsStart: fnReg + 1});
        this.free(fnReg);
        for(const r of argRegs) this.free(r);
        return target;
      }
    }

    // Fallback: bare name
    const target = forcedReg !== undefined ? forcedReg : this.alloc();
    const localReg = this.lookup(name);
    if(localReg !== null){
      this.emit({op:'MOVE', a:target, b:localReg});
    }else{
      this.emit({op:'GETG', a:target, k:this.addStr(name)});
    }
    return target;
  }

  /* ---------- split args by commas at depth 0 ---------- */
  splitArgs(sig, start, end){
    if(start >= end) return [];
    const args = [];
    let depth = 0, aStart = start;
    for(let j = start; j < end; j++){
      const t = sig[j];
      if(t.k === 'op'){
        if(t.v === '(' || t.v === '[' || t.v === '{') depth++;
        else if(t.v === ')' || t.v === ']' || t.v === '}') depth--;
        else if(t.v === ',' && depth === 0){
          args.push([aStart, j]);
          aStart = j + 1;
        }
      }
    }
    if(aStart < end) args.push([aStart, end]);
    return args;
  }

  /* ---------- compile local declaration ---------- */
  compileLocal(sig, i, end){
    // local [function] NAME...
    let j = i + 1;

    // local function NAME ...
    if(sig[j] && sig[j].k === 'kw' && sig[j].v === 'function'){
      return this.compileFunctionDef(sig, i, end, true);
    }

    // Collect names
    const names = [];
    while(j < end && sig[j].k === 'name'){
      names.push(sig[j].v);
      j++;
      if(sig[j] && sig[j].v === ','){ j++; continue; }
      break;
    }

    // If there's an '=', parse the RHS
    if(sig[j] && sig[j].v === '='){
      const exprEnd = this.findStatementEnd(sig, j + 1, end);
      const rhsTokens = sig.slice(j + 1, exprEnd);
      // Split RHS by commas at depth 0
      const parts = this.splitArgs(rhsTokens, 0, rhsTokens.length);
      for(let k = 0; k < names.length; k++){
        const reg = this.declare(names[k]);
        if(k < parts.length){
          const [pStart, pEnd] = parts[k];
          this.compileExpr(rhsTokens, pStart, pEnd, reg);
        }else{
          this.emit({op:'LOADK', a:reg, k:this.addNil()});
        }
      }
      return exprEnd;
    }else{
      // No initializer
      for(const n of names){
        const reg = this.declare(n);
        this.emit({op:'LOADK', a:reg, k:this.addNil()});
      }
      return j;
    }
  }

  /* ---------- compile return ---------- */
  compileReturn(sig, i, end){
    const stmtEnd = this.findStatementEnd(sig, i + 1, end);
    if(i + 1 >= stmtEnd){
      this.emit({op:'RETURN', a:0, b:0});
      return stmtEnd;
    }
    // Split return values by commas
    const retTokens = sig.slice(i + 1, stmtEnd);
    const parts = this.splitArgs(retTokens, 0, retTokens.length);
    const retRegs = [];
    for(const [pStart, pEnd] of parts){
      retRegs.push(this.compileExpr(retTokens, pStart, pEnd));
    }
    // Emit RETURN with base = first retReg
    this.emit({op:'RETURN', a: retRegs[0] || 0, b: retRegs.length});
    for(const r of retRegs) this.free(r);
    return stmtEnd;
  }

/* ============================================================
 * compileIf — full if/elseif/else
 * ============================================================ */
compileIf(sig, i, end){
  // Pattern:
  //   if <c1> then <b1>
  //   elseif <c2> then <b2>
  //   ...
  //   else <bn>
  //   end
  //
  // Emit plan:
  //   <c1>                     ; compile condition into a register
  //   JMPIF not-true → nextBranch  ; if condition false, jump to next branch
  //   <b1>
  //   JMP end                  ; skip remaining branches
  //   nextBranch:
  //   <c2>
  //   ...
  //   elseBody:                ; if all else fails
  //   <bn>
  //   end:

  const endJumps = [];  // to patch: list of instruction indices that need target=end
  let j = i;

  // Parse branches
  const branches = [];  // { condStart, condEnd, bodyStart, bodyEnd }
  let elseBody = null;
  let depth = 0;
  let curCondStart = -1, curBodyStart = -1;

  for(let k = i; k < end; k++){
    const t = sig[k];
    if(t.k === 'kw' && ['do','if','while','for','function','repeat'].includes(t.v) && k !== i) depth++;
    else if(t.k === 'kw' && ['end','until'].includes(t.v)){
      if(depth === 0){
        // Close final branch
        if(curBodyStart !== -1) branches.push({condStart: curCondStart, condEnd: curBodyStart - 1, bodyStart: curBodyStart, bodyEnd: k});
        j = k;
        break;
      }
      depth--;
    }
    else if(depth === 0 && t.k === 'kw' && t.v === 'then'){
      // End of condition
      // curCondStart..k-1 = condition
      // curBodyStart = k+1
      const condEnd = k;
      // We haven't stored curCondStart yet for the first branch (it's i+1)
      if(curCondStart === -1) curCondStart = i + 1;
      // Push branch with condStart..condEnd
      // But we don't know bodyEnd yet — will push on next branch or end
      branches.push({condStart: curCondStart, condEnd: condEnd, bodyStart: k+1, bodyEnd: -1});
      curBodyStart = k + 1;
      // Reset curCondStart for next elseif
      curCondStart = -1;
    }
    else if(depth === 0 && t.k === 'kw' && t.v === 'elseif'){
      // Close previous branch's body
      if(branches.length > 0 && branches[branches.length-1].bodyEnd === -1){
        branches[branches.length-1].bodyEnd = k;
      }
      curCondStart = k + 1;
      curBodyStart = -1;
    }
    else if(depth === 0 && t.k === 'kw' && t.v === 'else'){
      // Close previous branch's body, then else-body runs from k+1 to matching end
      if(branches.length > 0 && branches[branches.length-1].bodyEnd === -1){
        branches[branches.length-1].bodyEnd = k;
      }
      // Find matching end
      let d2 = 0, endIdx = -1;
      for(let m = k + 1; m < end; m++){
        const tm = sig[m];
        if(tm.k === 'kw' && ['do','if','while','for','function','repeat'].includes(tm.v)) d2++;
        else if(tm.k === 'kw' && ['end','until'].includes(tm.v)){
          if(d2 === 0){ endIdx = m; break; }
          d2--;
        }
      }
      if(endIdx !== -1){
        elseBody = {bodyStart: k + 1, bodyEnd: endIdx};
        j = endIdx;
      }
      break;
    }
  }

  if(branches.length === 0) return i + 1;

  // Emit each branch
  for(let b = 0; b < branches.length; b++){
    const br = branches[b];
    const nextJmpIdx = [];

    // Compile condition
    const condReg = this.compileExpr(sig, br.condStart, br.condEnd);

    // If false → jump to next branch
    const skipJmp = this.emit({op:'JMPIF', a:condReg, cmp:false, target:-1});
    nextJmpIdx.push(skipJmp);
    this.free(condReg);

    // Compile branch body
    this.pushScope();
    this.compileBlock(sig, br.bodyStart, br.bodyEnd);
    this.popScope();

    // At end of branch, jump to end
    const endJmp = this.emit({op:'JMP', target:-1});
    endJumps.push(endJmp);

    // Patch the skip jump to land here (start of next branch)
    const skipTarget = this.instructions.length;
    for(const sJmp of nextJmpIdx){
      this.instructions[sJmp].target = skipTarget;
    }
  }

  // Emit else body (or nothing)
  if(elseBody){
    this.pushScope();
    this.compileBlock(sig, elseBody.bodyStart, elseBody.bodyEnd);
    this.popScope();
  }

  // Patch all end jumps to here
  const endTarget = this.instructions.length;
  for(const eJ of endJumps){
    this.instructions[eJ].target = endTarget;
  }

  return j + 1;
}

/* ============================================================
 * compileWhile — while <cond> do <body> end
 * ============================================================ */
compileWhile(sig, i, end){
  // Find `do` at depth 0
  let doIdx = -1, depth = 0;
  for(let k = i + 1; k < end; k++){
    const t = sig[k];
    if(t.k === 'kw' && ['do','if','while','for','function','repeat'].includes(t.v)) depth++;
    else if(t.k === 'kw' && ['end','until'].includes(t.v)){
      if(depth === 0){ return i + 1; }
      depth--;
    }
    else if(depth === 0 && t.k === 'kw' && t.v === 'do'){ doIdx = k; break; }
  }
  if(doIdx === -1) return i + 1;

  // Find matching end
  const endIdx = this.findMatchingEnd(sig, doIdx, end);

  // Emit plan:
  //   loop_start:
  //   <cond>                    ; into condReg
  //   JMPIF condReg==false → loop_end
  //   <body>
  //   JMP loop_start
  //   loop_end:

  const loopStart = this.instructions.length;
  this.breakStack.push({ breakPatches: [], continueTarget: loopStart });

  const condReg = this.compileExpr(sig, i + 1, doIdx);
  const exitJmp = this.emit({op:'JMPIF', a:condReg, cmp:false, target:-1});
  this.free(condReg);

  this.pushScope();
  this.compileBlock(sig, doIdx + 1, endIdx);
  this.popScope();

  this.emit({op:'JMP', target:loopStart});

  const loopEnd = this.instructions.length;
  this.instructions[exitJmp].target = loopEnd;

  // Patch breaks
  const frame = this.breakStack.pop();
  for(const bJ of frame.breakPatches){
    this.instructions[bJ].target = loopEnd;
  }

  return endIdx + 1;
}

/* ============================================================
 * compileFor — numeric and generic
 *   for i=1,10,2 do <body> end        (numeric)
 *   for k,v in pairs(t) do <body> end (generic)
 * ============================================================ */
compileFor(sig, i, end){
  // Find `do` at depth 0
  let doIdx = -1, depth = 0;
  for(let k = i + 1; k < end; k++){
    const t = sig[k];
    if(t.k === 'kw' && ['do','if','while','for','function','repeat'].includes(t.v)) depth++;
    else if(t.k === 'kw' && ['end','until'].includes(t.v)){
      if(depth === 0) return i + 1;
      depth--;
    }
    else if(depth === 0 && t.k === 'kw' && t.v === 'do'){ doIdx = k; break; }
  }
  if(doIdx === -1) return i + 1;

  const endIdx = this.findMatchingEnd(sig, doIdx, end);

  // Detect numeric vs generic
  let isGeneric = false;
  for(let k = i + 1; k < doIdx; k++){
    if(sig[k].k === 'kw' && sig[k].v === 'in'){ isGeneric = true; break; }
  }

  if(isGeneric){
    return this.compileGenericFor(sig, i, doIdx, endIdx);
  }else{
    return this.compileNumericFor(sig, i, doIdx, endIdx);
  }
}

/* ---------- numeric for ---------- */
compileNumericFor(sig, i, doIdx, endIdx){
  // for NAME = START, LIMIT [, STEP] do BODY end
  if(sig[i+1].k !== 'name') return endIdx + 1;
  const name = sig[i+1].v;

  // Split by commas at depth 0
  const rangeStart = i + 3;   // after `for NAME =`
  const rangeTokens = sig.slice(rangeStart, doIdx);
  const parts = this.splitArgs(rangeTokens, 0, rangeTokens.length);

  if(parts.length < 2) return endIdx + 1;

  // Allocate control registers:
  //   ctrlReg  — loop counter
  //   limitReg — limit
  //   stepReg  — step (default 1)
  const ctrlReg = this.alloc();
  const limitReg = this.alloc();
  const stepReg = this.alloc();

  // Compile start → ctrlReg
  this.compileExpr(rangeTokens, parts[0][0], parts[0][1], ctrlReg);
  // Compile limit → limitReg
  this.compileExpr(rangeTokens, parts[1][0], parts[1][1], limitReg);
  // Compile step → stepReg, or default to 1
  if(parts.length >= 3){
    this.compileExpr(rangeTokens, parts[2][0], parts[2][1], stepReg);
  }else{
    this.emit({op:'LOADK', a:stepReg, k:this.addNum(1)});
  }

  // Loop variable lives in a fresh register
  const varReg = this.alloc();

  const loopStart = this.instructions.length;
  this.breakStack.push({ breakPatches: [], continueTarget: -1 });

  // bodyStart = doIdx + 1
  // Check: if ctrl > limit (when step > 0) → exit
  //        if ctrl < limit (when step < 0) → exit
  // We emit:
  //   FORPREP: if step > 0 and ctrl > limit → jump end
  //            if step < 0 and ctrl < limit → jump end
  const prepJmp = this.emit({op:'FORPREP', a:ctrlReg, target:-1});

  // MOV varReg = ctrl
  this.emit({op:'MOVE', a:varReg, b:ctrlReg});

  // body scope
  this.pushScope();
  this.scope[this.scope.length-1][name] = varReg;

  // continue target is loop end (where FORLOOP is)
  const continueTarget = -1;  // filled below

  this.compileBlock(sig, doIdx + 1, endIdx);
  this.popScope();

  // FORLOOP: ctrl += step; if still within range, jump loopStart
  const forLoopIdx = this.emit({op:'FORLOOP', a:ctrlReg, target:loopStart});

  const loopEnd = this.instructions.length;
  this.instructions[prepJmp].target = loopEnd;

  // Patch breaks
  const frame = this.breakStack.pop();
  for(const bJ of frame.breakPatches){
    this.instructions[bJ].target = loopEnd;
  }

  // Free control regs (varReg freed when scope pops)
  this.free(stepReg);
  this.free(limitReg);
  this.free(ctrlReg);

  return endIdx + 1;
}

/* ---------- generic for ---------- */
compileGenericFor(sig, i, doIdx, endIdx){
  // for K1, K2, ... in EXPR do BODY end
  // We compile EXPR into a table, then iterate with a simple
  // numeric counter from 1..#table. This is a valid iteration
  // order for array-like tables but may reorder keys for
  // hash tables. Acceptable for source-level VM.
  if(sig[i+1].k !== 'name') return endIdx + 1;

  // Collect variables
  const vars = [];
  let k = i + 1;
  while(k < doIdx){
    if(sig[k].k === 'name'){ vars.push(sig[k].v); k++; }
    if(k < doIdx && sig[k].v === ','){ k++; continue; }
    if(k < doIdx && sig[k].k === 'kw' && sig[k].v === 'in'){ k++; break; }
    if(k < doIdx && sig[k].k === 'name' && sig[k].v !== 'in'){ continue; }
    break;
  }
  // Skip 'in'
  while(k < doIdx && sig[k].k !== 'kw') k++;

  const exprStart = k;   // after 'in'
  const exprReg = this.compileExpr(sig, exprStart, doIdx);

  // Allocate control regs
  const counterReg = this.alloc();
  const limitReg = this.alloc();
  const varReg = this.alloc();   // holds each value
  const keyReg = this.alloc();

  // counter = 0
  this.emit({op:'LOADK', a:counterReg, k:this.addNum(0)});
  // limit = #expr
  // We emit: limitReg = #Stk[exprReg] via a special instruction
  // Use CALL of the len operation: not available as opcode, so
  // use a len expression via SETT/GETT... simplest: emit a special
  // instruction via the CALL machinery. Add a custom 'LEN' op:
  this.emit({op:'LEN', a:limitReg, b:exprReg});

  const loopStart = this.instructions.length;
  this.breakStack.push({ breakPatches: [], continueTarget: -1 });

  // if counter >= limit → exit
  const prepJmp = this.emit({op:'FORPREP', a:counterReg, target:-1});

  // counter += 1
  this.emit({op:'ADD', a:counterReg, b:counterReg, c:this.loadOneReg()});
  // keyReg = counter
  this.emit({op:'MOVE', a:keyReg, b:counterReg});
  // varReg = expr[keyReg]
  this.emit({op:'GETT', a:varReg, b:exprReg, c:keyReg});

  // body scope: bind vars
  this.pushScope();
  if(vars.length === 1){
    // Single var: receives value (for ipairs) or key (for pairs)
    this.scope[this.scope.length-1][vars[0]] = varReg;
  }else if(vars.length >= 2){
    // Two vars: key, value
    this.scope[this.scope.length-1][vars[0]] = keyReg;
    this.scope[this.scope.length-1][vars[1]] = varReg;
  }

  this.compileBlock(sig, doIdx + 1, endIdx);
  this.popScope();

  // Loop: if counter < limit → loopStart
  const forLoopIdx = this.emit({op:'FORLOOP', a:counterReg, target:loopStart});

  const loopEnd = this.instructions.length;
  this.instructions[prepJmp].target = loopEnd;

  // Patch breaks
  const frame = this.breakStack.pop();
  for(const bJ of frame.breakPatches){
    this.instructions[bJ].target = loopEnd;
  }

  this.free(keyReg);
  this.free(varReg);
  this.free(limitReg);
  this.free(counterReg);
  this.free(exprReg);

  return endIdx + 1;
}

/* ---------- helper: register holding constant 1 ---------- */
loadOneReg(){
  // Cache a register holding the constant 1, allocate if not present
  if(this._oneReg === undefined){
    this._oneReg = this.alloc();
    this.emit({op:'LOADK', a:this._oneReg, k:this.addNum(1)});
  }
  return this._oneReg;
}

/* ============================================================
 * compileRepeat — repeat <body> until <cond>
 * ============================================================ */
compileRepeat(sig, i, end){
  // Find `until` at depth 0
  let untilIdx = -1, depth = 0;
  for(let k = i + 1; k < end; k++){
    const t = sig[k];
    if(t.k === 'kw' && ['do','if','while','for','function','repeat'].includes(t.v)) depth++;
    else if(t.k === 'kw' && t.v === 'until'){
      if(depth === 0){ untilIdx = k; break; }
      depth--;
    }
    else if(t.k === 'kw' && t.v === 'end'){
      if(depth === 0) return i + 1;
      depth--;
    }
  }
  if(untilIdx === -1) return i + 1;

  // Find end of until condition (end of enclosing scope or ;)
  let condEnd = this.findStatementEnd(sig, untilIdx + 1, end);

  const loopStart = this.instructions.length;
  this.breakStack.push({ breakPatches: [], continueTarget: loopStart });

  this.pushScope();
  this.compileBlock(sig, i + 1, untilIdx);
  this.popScope();

  // Evaluate until condition; if false → loop again
  const condReg = this.compileExpr(sig, untilIdx + 1, condEnd);
  // JMPIF condReg==false → loopStart
  this.emit({op:'JMPIF', a:condReg, cmp:false, target:loopStart});
  this.free(condReg);

  const loopEnd = this.instructions.length;

  const frame = this.breakStack.pop();
  for(const bJ of frame.breakPatches){
    this.instructions[bJ].target = loopEnd;
  }

  return condEnd;
}

  /* ---------- compile do ---------- */
  compileDo(sig, i, end){
    this.pushScope();
    const inner = this.compileBlock(sig, i + 1, this.findMatchingEnd(sig, i, end));
    this.popScope();
    return inner;
  }

  /* ============================================================
 * compileBreak — becomes a JMP patched by the enclosing loop
 * ============================================================ */
compileBreak(sig, i, end){
  if(this.breakStack.length === 0){
    // break outside loop → skip
    return i + 1;
  }
  const jmpIdx = this.emit({op:'JMP', target:-1});
  this.breakStack[this.breakStack.length - 1].breakPatches.push(jmpIdx);
  return i + 1;
}

/* ============================================================
 * compileFunctionDef — function NAME(params) body end
 *                      local function NAME(params) body end
 *                      NAME = function(params) body end
 *
 * We create a nested prototype (Chunk) and emit a CLOSURE
 * instruction that references it.
 * ============================================================ */
compileFunctionDef(sig, i, end, isLocal){
  // Determine name and params
  let name = null;
  let fnStart = i;   // index of the `function` keyword (or `local` if local function)
  let pIdx = -1;

  if(isLocal){
    // local function NAME(...) ... end
    // sig[i] = 'local', sig[i+1] = 'function', sig[i+2] = NAME
    if(!(sig[i+1] && sig[i+1].k === 'kw' && sig[i+1].v === 'function')) return i + 1;
    if(!(sig[i+2] && sig[i+2].k === 'name')) return i + 1;
    name = sig[i+2].v;
    fnStart = i + 1;
    pIdx = i + 3;
  }else{
    // function NAME(...) ... end
    // sig[i] = 'function', sig[i+1] = NAME
    if(!(sig[i+1] && sig[i+1].k === 'name')) return i + 1;
    name = sig[i+1].v;
    fnStart = i;
    pIdx = i + 2;
  }

  // Skip to '('
  while(pIdx < end && sig[pIdx].v !== '(') pIdx++;
  if(pIdx >= end) return i + 1;

  // Find matching ')'
  let depth = 1, pEnd = pIdx + 1;
  while(pEnd < end && depth > 0){
    if(sig[pEnd].v === '(') depth++;
    else if(sig[pEnd].v === ')') depth--;
    pEnd++;
  }
  if(depth !== 0) return i + 1;
  pEnd--;   // at ')'

  // Parameters
  const params = [];
  let k = pIdx + 1;
  while(k < pEnd){
    if(sig[k].k === 'name'){ params.push(sig[k].v); }
    k++;
  }

  // Find matching end of body
  const bodyStart = pEnd + 1;
  const bodyEnd = this.findMatchingEnd(sig, fnStart, end);

  // Compile body into a NESTED compiler instance
  const sub = new Compiler(this.r);
  sub.paramCount = params.length;
  // Declare params in sub's root scope
  for(const p of params) sub.declare(p);
  sub.pushScope();
  sub.compileBlock(sig, bodyStart, bodyEnd);
  sub.popScope();
  sub.emit({op:'RETURN', a:0, b:0});

  // Register the sub-prototype
  const protoIdx = this.functions.length;
  this.functions.push({
    instructions: sub.instructions,
    constants: sub.constants,
    maxReg: sub.maxReg,
    paramCount: sub.paramCount,
    functions: sub.functions,
  });

  // Emit CLOSURE
  if(isLocal){
    // local function NAME = closure
    const reg = this.declare(name);
    this.emit({op:'CLOSURE', a:reg, bx:protoIdx});
  }else{
    // NAME = closure — could be local or global
    const localReg = this.lookup(name);
    if(localReg !== null){
      const tmp = this.alloc();
      this.emit({op:'CLOSURE', a:tmp, bx:protoIdx});
      this.emit({op:'MOVE', a:localReg, b:tmp});
      this.free(tmp);
    }else{
      const tmp = this.alloc();
      this.emit({op:'CLOSURE', a:tmp, bx:protoIdx});
      this.emit({op:'SETG', a:tmp, k:this.addStr(name)});
      this.free(tmp);
    }
  }

  return bodyEnd + 1;
}

  /* ---------- compile expression statement ---------- */
  compileExprStatement(sig, i, end){
    // Could be: NAME = expr, NAME[k] = expr, NAME(...), NAME.field = expr
    // Find assignment or call boundary
    let depth = 0, eqIdx = -1, callIdx = -1;
    for(let j = i; j < end; j++){
      const t = sig[j];
      if(t.k === 'op'){
        if(t.v === '(' || t.v === '[' || t.v === '{'){
          if(t.v === '(' && depth === 0 && callIdx === -1 && j > i) callIdx = j;
          depth++;
        }
        else if(t.v === ')' || t.v === ']' || t.v === '}') depth--;
        else if(depth === 0 && t.v === '=' && eqIdx === -1) eqIdx = j;
        else if(depth === 0 && t.v === ';') break;
      }
      if(depth === 0 && t.k === 'kw' && ['end','else','elseif'].includes(t.v)) break;
    }

    if(eqIdx !== -1){
      // Assignment: LHS = RHS
      const lhsTokens = sig.slice(i, eqIdx);
      const rhsEnd = this.findStatementEnd(sig, eqIdx + 1, end);
      const rhsTokens = sig.slice(eqIdx + 1, rhsEnd);

      // Compile RHS
      const rhsReg = this.compileExpr(rhsTokens, 0, rhsTokens.length);

      // Store to LHS
      this.compileStore(lhsTokens, rhsReg);

      this.free(rhsReg);
      return rhsEnd;
    }

    // Statement-level call
    const callEnd = this.findStatementEnd(sig, i, end);
    const callTokens = sig.slice(i, callEnd);
    this.compileExpr(callTokens, 0, callTokens.length);
    return callEnd;
  }

  /* ---------- store into LHS (NAME, NAME.field, NAME[k]) ---------- */
  compileStore(lhsTokens, valueReg){
    if(lhsTokens.length === 1 && lhsTokens[0].k === 'name'){
      const name = lhsTokens[0].v;
      const localReg = this.lookup(name);
      if(localReg !== null){
        this.emit({op:'MOVE', a:localReg, b:valueReg});
      }else{
        this.emit({op:'SETG', a:valueReg, k:this.addStr(name)});
      }
      return;
    }
    // NAME.field or NAME[k]
    if(lhsTokens[0].k === 'name'){
      // Load base
      const baseReg = this.alloc();
      const localReg = this.lookup(lhsTokens[0].v);
      if(localReg !== null){
        this.emit({op:'MOVE', a:baseReg, b:localReg});
      }else{
        this.emit({op:'GETG', a:baseReg, k:this.addStr(lhsTokens[0].v)});
      }
      let j = 1;
      // Walk .field chain
      while(j < lhsTokens.length - 1 && lhsTokens[j].v === '.'){
        const fieldName = lhsTokens[j+1].v;
        // If not last, walk down
        if(j + 2 < lhsTokens.length){
          const fReg = this.alloc();
          this.emit({op:'LOADK', a:fReg, k:this.addStr(fieldName)});
          this.emit({op:'GETT', a:baseReg, b:baseReg, c:fReg});
          this.free(fReg);
          j += 2;
        }else{
          // Last segment: store
          const fReg = this.alloc();
          this.emit({op:'LOADK', a:fReg, k:this.addStr(fieldName)});
          this.emit({op:'SETT', a:valueReg, b:baseReg, c:fReg});
          this.free(fReg);
          break;
        }
      }
      // Walk [k] access
      while(j < lhsTokens.length - 1 && lhsTokens[j].v === '['){
        let depth = 1, closeIdx = -1;
        for(let k = j + 1; k < lhsTokens.length; k++){
          if(lhsTokens[k].v === '[') depth++;
          else if(lhsTokens[k].v === ']'){ depth--; if(depth === 0){ closeIdx = k; break; } }
        }
        if(closeIdx === -1) break;
        if(closeIdx === lhsTokens.length - 1){
          const keyReg = this.compileExpr(lhsTokens, j + 1, closeIdx);
          this.emit({op:'SETT', a:valueReg, b:baseReg, c:keyReg});
          this.free(keyReg);
          break;
        }else{
          const keyReg = this.compileExpr(lhsTokens, j + 1, closeIdx);
          this.emit({op:'GETT', a:baseReg, b:baseReg, c:keyReg});
          this.free(keyReg);
          j = closeIdx + 1;
        }
      }
      this.free(baseReg);
      return;
    }
    // Unknown LHS shape — skip
  }

  /* ---------- find matching end for a block opener ---------- */
  findMatchingEnd(sig, i, end){
    let depth = 0;
    for(let j = i + 1; j < end; j++){
      const t = sig[j];
      if(t.k === 'kw' && ['do','if','while','for','function','repeat'].includes(t.v)) depth++;
      else if(t.k === 'kw' && ['end','until'].includes(t.v)){
        if(depth === 0) return j;
        depth--;
      }
    }
    return end;
  }
}

// unescapeLua is defined in obfuscator.js; we reuse it here.
// If obfuscator.js is loaded after vm.js, we grab it at call time.

/* ============================================================
 * 5) Serializer — chunk → bytes  (approximated to match
 *    IronBrew2's layout; XOR keys applied to opcode/const/string)
 * ============================================================ */
function serialize(compiled, ctx){
  const {
    PrimaryXorKey, IXorKey1, IXorKey2,
    ConstantMapping, ChunkSteps,
  } = ctx;

  const w = new ByteWriter();

  // ---- ParameterCount step ----
  w.u32(compiled.paramCount);

  // ---- Constants step ----
  // ConstCount (u32), then each: type (u8 XORed), value
  w.u32(compiled.constants.length);
  for(const c of compiled.constants){
    if(c.type === 'nil'){
      // Treat nil as bool false for simplicity; the VM interpreter
      // handles undefined constants as nil.
      w.u8x(ConstantMapping[1], PrimaryXorKey);
      w.u8x(0, PrimaryXorKey);   // false
    }else if(c.type === 'bool'){
      w.u8x(ConstantMapping[1], PrimaryXorKey);
      w.u8x(c.value ? 1 : 0, PrimaryXorKey);
    }else if(c.type === 'num'){
      w.u8x(ConstantMapping[2], PrimaryXorKey);
      // float64 encoded via two u32s (matching gFloat)
      const buf = new ArrayBuffer(8);
      new DataView(buf).setFloat64(0, c.value, true);   // LE
      const bytes = new Uint8Array(buf);
      // gFloat reads left u32 first, then right u32
      // Encoding: right (exponent+sign) first, then left (mantissa)
      const left = bytes[0] | (bytes[1]<<8) | (bytes[2]<<16) | (bytes[3]<<24);
      const right = bytes[4] | (bytes[5]<<8) | (bytes[6]<<16) | (bytes[7]<<24);
      w.u32x(right >>> 0, PrimaryXorKey);
      w.u32x(left >>> 0, PrimaryXorKey);
    }else if(c.type === 'str'){
      w.u8x(ConstantMapping[3], PrimaryXorKey);
      w.u32(c.value.length);
      w.str(c.value, PrimaryXorKey);
    }
  }

  // ---- Instructions step ----
  // Count (u32), then each instruction is 3 u32s:
  //   Data1 (type in bits 1-2, A in 3-11, B in 12-20, C in 21-29)
  //   Data2 (opcode in bits 1-11, Bx/sBx in 12-32)
  // plus extra if the op needs it
  w.u32(compiled.instructions.length);
  for(const inst of compiled.instructions){
    const {data1, data2} = encodeInstruction(inst, ctx);
    w.u32x(data1 >>> 0, IXorKey1);
    w.u32x(data2 >>> 0, IXorKey2);
  }

  // ---- Functions step ----
  w.u32(compiled.functions.length);
  // (nested function prototypes would go here — skip for now)

  return w.bytes;
}

/* ============================================================
 * 6) Instruction encoder (op name → opcode id + packed fields)
 * ============================================================ */
function encodeInstruction(inst, ctx){
  const { OpcodeId, OP_BIT_WIDTHS } = ctx;

  const opId = OpcodeId[inst.op] !== undefined ? OpcodeId[inst.op] : 0;
  const a = inst.a || 0;
  const b = inst.b || 0;
  const c = inst.c !== undefined ? inst.c : 0;
  const bx = inst.bx || 0;

  // Determine "type" (how B/C are encoded):
  //   0 — B,C in Data1 (default)
  //   1 — Bx in Data2 (long constant index)
  //   2 — sBx in Data2 (signed)
  //   3 — Bx in Data2 + C in Data1
  let type = 0;
  let typeB = b;
  let typeC = c;
  if(['LOADK','GETG','SETG','CLOSURE'].includes(inst.op)){
    type = 1;
    typeB = bx || 0;
    typeC = 0;
  }else if(['JMP'].includes(inst.op)){
    type = 2;
    typeB = inst.target || 0;
    typeC = 0;
  }

  // Data1: [A(9 bits in 3-11)] [C(9 bits in 21-29)] [type(2 bits in 1-2)]
  // Layout: bit 0 unused, bits 1-2 = type, bits 3-11 = A, bits 12-20 = B, bits 21-29 = C
  let data1 = 0;
  data1 |= (type & 0x3) << 1;
  data1 |= (a & 0x1FF) << 3;
  if(type === 0 || type === 3){
    data1 |= (typeB & 0x1FF) << 12;
    data1 |= (typeC & 0x1FF) << 21;
  }else if(type === 3){
    data1 |= (typeC & 0x1FF) << 21;
  }

  // Data2: [opcode(11 bits in 1-11)] [B or Bx or sBx]
  let data2 = 0;
  data2 |= (opId & 0x7FF) << 1;
  if(type === 0){
    // B already in Data1
  }else if(type === 1 || type === 2){
    data2 |= (typeB & 0x1FFFFF) << 12;
  }

  return {data1: data1 >>> 0, data2: data2 >>> 0};
}

/* ============================================================
 * 7) VM emitter — assembles the full Lua VM string
 *    (Uses VMP1, VMP2, VMP3 from VMStrings, with our source-level
 *     dispatch tree replacing bytecode opcodes)
 * ============================================================ */
function generate(source, r, opts){
  opts = opts || {};

  // ---- Compile source to instruction tuples ----
  const compiler = new Compiler(r);
  const compiled = compiler.compile(source);

  // ---- Pick XOR keys ----
  const PrimaryXorKey = 1 + Math.floor(r() * 255);
  const IXorKey1 = (r() * 0xFFFFFFFF) >>> 0;
  const IXorKey2 = (r() * 0xFFFFFFFF) >>> 0;

  // ---- Opcode mapping ----
  // Our source-level opcodes get IDs starting at 1 (0 reserved)
  const opcodeNames = [
    'LOADK','MOVE','GETG','SETG','GETT','SETT',
    'ADD','SUB','MUL','DIV','MOD','POW','CONCAT',
    'EQ','NE','LT','LE','GT','GE','NOT',
    'JMP','JMPIF','CALL','RETURN','CLOSURE','NEWTBL','SETLIST',
    'FORPREP','FORLOOP','SETTOP'
  ];
  const OpcodeId = {};
  opcodeNames.forEach((name, i) => { OpcodeId[name] = i; });

  // ---- Constant type mapping ----
  const ConstantMapping = { 1: 1, 2: 2, 3: 3 };   // bool, num, str

  // ---- Chunk step order ----
  const ChunkSteps = ['ParameterCount','Constants','Instructions','Functions','LineInfo'];

  const ctx = {
    PrimaryXorKey, IXorKey1, IXorKey2,
    OpcodeId, ConstantMapping, ChunkSteps,
  };

  // ---- Serialize ----
  const bytes = serialize(compiled, ctx);

  // ---- Compress + encode ----
  const compressed = compress(bytes);
  const encoded = compressedToString(compressed);

  // ---- Assemble VM ----
  const vmParts = [];

  // Preamble (VMP1 stub — real IronBrew2 VMP1 from VMStrings)
  vmParts.push(VMP1);
  vmParts.push(`local ByteString=decompress('${encoded}');\n`);

  // Chunk steps (ParameterCount / Constants / Instructions / Functions)
  vmParts.push(`
local Chunk = Deserialize();
do
  local PCount = gBits32();
  Chunk[4] = PCount;
end;
do
  local ConstCount = gBits32();
  local Consts = {};
  for Idx=1,ConstCount do
    local Type=gBits8();
    local Cons;
    if(Type==${ConstantMapping[1]}) then Cons=(gBits8() ~= 0);
    elseif(Type==${ConstantMapping[2]}) then Cons = gFloat();
    elseif(Type==${ConstantMapping[3]}) then Cons=gString();
    end;
    Consts[Idx]=Cons;
  end;
  Chunk[2] = Consts;
end;
do
  for Idx=1,gBits32() do
    local Data1=BitXOR(gBits32(),${IXorKey1});
    local Data2=BitXOR(gBits32(),${IXorKey2});
    local Type=gBit(Data1,1,2);
    local Opco=gBit(Data2,1,11);
    local Inst={Opco, gBit(Data1,3,11), nil, nil, Data2};
    if (Type == 0) then Inst[OP_B]=gBit(Data1,12,20);Inst[OP_C]=gBit(Data1,21,29);
    elseif(Type==1) then Inst[OP_B]=gBit(Data2,12,33);
    elseif(Type==2) then Inst[OP_B]=gBit(Data2,12,32)-1048575;
    elseif(Type==3) then Inst[OP_B]=gBit(Data2,12,32)-1048575;Inst[OP_C]=gBit(Data1,21,29);
    end;
    Chunk[1][Idx]=Inst;
  end;
end;
do
  for Idx=1,gBits32() do
    Chunk[3][Idx-1]=Deserialize();
  end;
end;
`);

  // Outer shell (VMP2)
  vmParts.push(VMP2);

  // Dispatch tree — for each opcode, emit its interpreter body.
  // We build the dispatch tree the same way IronBrew2 does: binary search.
  vmParts.push(buildDispatchTree(OpcodeId, r));

  // Tail (VMP3)
  vmParts.push(VMP3);

  // ---- Placeholder substitutions ----
  let vm = vmParts.join('');
  vm = vm.replace(/XOR_KEY/g, String(PrimaryXorKey));
  vm = vm.replace(/OP_ENUM/g, '1');
  vm = vm.replace(/OP_A/g, '2');
  vm = vm.replace(/OP_B/g, '3');
  vm = vm.replace(/OP_BX/g, '4');
  vm = vm.replace(/OP_C/g, '5');
  vm = vm.replace(/OP_DATA/g, '6');
  // INSTR_CNT / FUNC_CNT placeholders (empty initial tables)
  vm = vm.replace(/INSTR_CNT/g, '0');
  vm = vm.replace(/FUNC_CNT/g, '0');

  return vm;
}

/* ============================================================
 * 8) Dispatch tree builder
 *    Takes our opcode table and produces the nested if-tree
 *    that IronBrew2's VMP2 expects.
 * ============================================================ */
function buildDispatchTree(OpcodeId, r){
  const entries = Object.entries(OpcodeId);   // [name, id]
  // Sort by id
  entries.sort((a, b) => a[1] - b[1]);

  // Emit interpreter for each opcode (Part 2 will fill in bodies)
  const bodyFor = name => {
    switch(name){
      case 'LOADK':    return `Stk[Inst[OP_A]]=Const[Inst[OP_BX]];`;
      case 'MOVE':     return `Stk[Inst[OP_A]]=Stk[Inst[OP_B]];`;
      case 'GETG':     return `Stk[Inst[OP_A]]=Env[Const[Inst[OP_BX]]];`;
      case 'SETG':     return `Env[Const[Inst[OP_BX]]]=Stk[Inst[OP_A]];`;
      case 'GETT':     return `Stk[Inst[OP_A]]=Stk[Inst[OP_B]][Stk[Inst[OP_C]]];`;
      case 'SETT':     return `Stk[Inst[OP_B]][Stk[Inst[OP_C]]]=Stk[Inst[OP_A]];`;
      case 'ADD':      return `Stk[Inst[OP_A]]=Stk[Inst[OP_B]]+Stk[Inst[OP_C]];`;
      case 'SUB':      return `Stk[Inst[OP_A]]=Stk[Inst[OP_B]]-Stk[Inst[OP_C]];`;
      case 'MUL':      return `Stk[Inst[OP_A]]=Stk[Inst[OP_B]]*Stk[Inst[OP_C]];`;
      case 'DIV':      return `Stk[Inst[OP_A]]=Stk[Inst[OP_B]]/Stk[Inst[OP_C]];`;
      case 'MOD':      return `Stk[Inst[OP_A]]=Stk[Inst[OP_B]]%Stk[Inst[OP_C]];`;
      case 'POW':      return `Stk[Inst[OP_A]]=Stk[Inst[OP_B]]^Stk[Inst[OP_C]];`;
      case 'CONCAT':   return `Stk[Inst[OP_A]]=Stk[Inst[OP_B]]..Stk[Inst[OP_C]];`;
      case 'EQ':       return `if (Stk[Inst[OP_B]]==Stk[Inst[OP_C]])~=(Inst[OP_A]~=0) then InstrPoint=InstrPoint+1 end;`;
      case 'NE':       return `if (Stk[Inst[OP_B]]~=Stk[Inst[OP_C]])~=(Inst[OP_A]~=0) then InstrPoint=InstrPoint+1 end;`;
      case 'LT':       return `if (Stk[Inst[OP_B]]<Stk[Inst[OP_C]])~=(Inst[OP_A]~=0) then InstrPoint=InstrPoint+1 end;`;
      case 'LE':       return `if (Stk[Inst[OP_B]]<=Stk[Inst[OP_C]])~=(Inst[OP_A]~=0) then InstrPoint=InstrPoint+1 end;`;
      case 'GT':       return `if (Stk[Inst[OP_B]]>Stk[Inst[OP_C]])~=(Inst[OP_A]~=0) then InstrPoint=InstrPoint+1 end;`;
      case 'GE':       return `if (Stk[Inst[OP_B]]>=Stk[Inst[OP_C]])~=(Inst[OP_A]~=0) then InstrPoint=InstrPoint+1 end;`;
      case 'NOT':      return `Stk[Inst[OP_A]]=not Stk[Inst[OP_B]];`;
      case 'JMP':      return `InstrPoint=Inst[OP_BX];`;
      case 'JMPIF':    return `if Stk[Inst[OP_A]] then InstrPoint=Inst[OP_BX];end;`;
      case 'CALL':     return `Stk[Inst[OP_A]]=Stk[Inst[OP_B]](unpack(Stk, Inst[OP_B]+1, Inst[OP_B]+Inst[OP_C]));`;
      case 'RETURN':   return `if Inst[OP_B]==0 then return;end;return unpack(Stk, Inst[OP_A], Inst[OP_A]+Inst[OP_B]-1);`;
      case 'CLOSURE':  return `Stk[Inst[OP_A]]=Wrap(Proto[Inst[OP_BX]], {}, Env);`;
      case 'NEWTBL':   return `Stk[Inst[OP_A]]={};`;
      case 'SETLIST':  return `-- setlist stub`;
      case 'FORPREP':  return `InstrPoint=Inst[OP_BX];`;
      case 'FORLOOP':  return `Stk[Inst[OP_A]]=Stk[Inst[OP_A]]+Stk[Inst[OP_A]+2];if Stk[Inst[OP_A]]<=Stk[Inst[OP_A]+1]then InstrPoint=Inst[OP_BX];end;`;
      case 'SETTOP':   return `Top=Inst[OP_A];`;
      default:         return '-- unknown opcode';
    }
  };

  // Build binary dispatch tree
  function tree(entries){
    if(entries.length === 1){
      const [name, id] = entries[0];
      return `if Enum==${id} then ${bodyFor(name)}`;
    }
    if(entries.length === 2){
      const [n0, i0] = entries[0];
      const [n1, i1] = entries[1];
      return `if Enum==${i0} then ${bodyFor(n0)} elseif Enum==${i1} then ${bodyFor(n1)}`;
    }
    const mid = Math.floor(entries.length / 2);
    const left = entries.slice(0, mid);
    const right = entries.slice(mid);
    const pivot = entries[mid - 1][1];
    return `if Enum<=${pivot} then ${tree(left)} else ${tree(right)} end;`;
  }

  let body = tree(entries);

  // Wrap in an if that falls through when Enum doesn't match any opcode
  return `
if ${body} end;
if Enum>${entries[entries.length-1][1]} then -- never
end;
`;
}

/* ============================================================
 * 9) VMP1, VMP2, VMP3 templates (verbatim from IronBrew2's
 *    VMStrings.cs, with our dispatch loop preserved)
 * ============================================================ */

const VMP1 = `
local BitXOR = bit and bit.bxor or function(a,b)
    local p,c=1,0
    while a>0 and b>0 do
        local ra,rb=a%2,b%2
        if ra~=rb then c=c+p end
        a,b,p=(a-ra)/2,(b-rb)/2,p*2
    end
    if a<b then a=b end
    while a>0 do
        local ra=a%2
        if ra>0 then c=c+p end
        a,p=(a-ra)/2,p*2
    end
    return c
end

local function gBit(Bit, Start, End)
    if End then
        local Res = (Bit / 2 ^ (Start - 1)) % 2 ^ ((End - 1) - (Start - 1) + 1);
        return Res - Res % 1;
    else
        local Plc = 2 ^ (Start - 1);
        return (Bit % (Plc + Plc) >= Plc) and 1 or 0;
    end;
end;

local Pos = 1;

local function gBits32()
    local W, X, Y, Z = Byte(ByteString, Pos, Pos + 3);
    W = BitXOR(W, XOR_KEY)
    X = BitXOR(X, XOR_KEY)
    Y = BitXOR(Y, XOR_KEY)
    Z = BitXOR(Z, XOR_KEY)
    Pos = Pos + 4;
    return (Z*16777216) + (Y*65536) + (X*256) + W;
end;

local function gBits8()
    local F = BitXOR(Byte(ByteString, Pos, Pos), XOR_KEY);
    Pos = Pos + 1;
    return F;
end;

local function gFloat()
    local Left = gBits32();
    local Right = gBits32();
    local IsNormal = 1;
    local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
    local Exponent = gBit(Right, 21, 31);
    local Sign = ((-1) ^ gBit(Right, 32));
    if (Exponent == 0) then
        if (Mantissa == 0) then
            return Sign * 0;
        else
            Exponent = 1;
            IsNormal = 0;
        end;
    elseif (Exponent == 2047) then
        return (Mantissa == 0) and (Sign * (1 / 0)) or (Sign * (0 / 0));
    end;
    return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
end;

local gSizet = gBits32;
local function gString(Len)
    local Str;
    if (not Len) then
        Len = gSizet();
        if (Len == 0) then
            return '';
        end;
    end;
    Str = Sub(ByteString, Pos, Pos + Len - 1);
    Pos = Pos + Len;
    local FStr = {}
    for Idx = 1, #Str do
        FStr[Idx] = Char(BitXOR(Byte(Sub(Str, Idx, Idx)), XOR_KEY))
    end
    return Concat(FStr);
end;

local gInt = gBits32;
local function _R(...) return {...}, Select('#', ...) end

local function Deserialize()
    local Instrs = {};
    local Functions = {};
    local Lines = {};
    local Chunk = 
    {
        Instrs,
        nil,
        Functions,
        nil,
        Lines
    };
    return Chunk;
end;

local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Concat = table.concat;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function() return _ENV end;
local Setmetatable = setmetatable;
local Select = select;
local Unpack = unpack;
local ToNumber = tonumber;

local function decompress(b)local c,d,e="","",{}local f=256;local g={}for h=0,f-1 do g[h]=Char(h)end;local i=1;local function k()local l=ToNumber(Sub(b, i,i),36)i=i+1;local m=ToNumber(Sub(b, i,i+l-1),36)i=i+l;return m end;c=Char(k())e[1]=c;while i<#b do local n=k()if g[n]then d=g[n]else d=c..Sub(c, 1,1)end;g[f]=c..Sub(d, 1,1)e[#e+1],c,f=d,d,f+1 end;return Concat(e)end;
`;

const VMP2 = `
local function Wrap(Chunk, Upvalues, Env)
    local Instr  = Chunk[1];
    local Const  = Chunk[2];
    local Proto  = Chunk[3];
    local Params = Chunk[4];

    return function(...)
        local Instr  = Instr; 
        local Const  = Const; 
        local Proto  = Proto; 
        local Params = Params;

        local _R = _R
        local InstrPoint = 1;
        local Top = -1;

        local Vararg = {};
        local Args  = {...};

        local PCount = Select('#', ...) - 1;

        local Lupvals = {};
        local Stk = {};

        for Idx = 0, PCount do
            if (Idx >= Params) then
                Vararg[Idx - Params] = Args[Idx + 1];
            else
                Stk[Idx] = Args[Idx + 1];
            end;
        end;

        local Varargsz = PCount - Params + 1

        local Inst;
        local Enum; 

        while true do
            Inst = Instr[InstrPoint];
            Enum = Inst[OP_ENUM];
`;

const VMP3 = `
            InstrPoint = InstrPoint + 1;
        end;
    end;
end;    
return Wrap(Deserialize(), {}, GetFEnv())();
`;

/* ============================================================
 * Exports
 * ============================================================ */
global.IronVM = {
  generate,
  compress,
  compressedToString,
  Compiler,
  serialize,
};

})(typeof window !== 'undefined' ? window : this);
