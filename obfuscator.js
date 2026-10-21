/* Lua 5.1 Obfuscator — full client-side implementation.
 *
 * Features:
 *   - Full Lua 5.1 tokenizer (long strings, comments, all operators, hex)
 *   - Scope-aware local/param renaming (handles shadowing)
 *   - String literal encryption (runtime decode via string.char)
 *   - Number literal encoding (arithmetic decomposition)
 *   - Smart minify: single space ONLY where the lexer requires it
 *   - Junk-code injection (do..end isolated)
 *   - Control-flow-flattening visual prefix
 *   - Fake decompiler prologue (decompiler bait)
 *   - Anti-tamper guard (prints "dtc" on detection)
 *   - VM-style loader with UPPERCASE hex payload wrapped in ('...')
 *   - Reference-style nested dispatch chain in the tail
 *   - IronBrew2 source-level VM (when opts.vm is on, replaces loader)
 *   - Zero-whitespace payload
 */
(function(global){
'use strict';

/* ============================ RNG ============================ */
function hashStr(s){
  let h=2166136261>>>0;
  for(let i=0;i<s.length;i++){h^=s.charCodeAt(i);h=Math.imul(h,16777619)>>>0;}
  return h>>>0;
}
function mulberry32(a){
  return function(){
    a|=0;a=(a+0x6D2B79F5)|0;
    let t=Math.imul(a^(a>>>15),1|a);
    t=(t+Math.imul(t^(t>>>7),61|t))^t;
    return ((t^(t>>>14))>>>0)/4294967296;
  };
}
function rng(seed){return seed?mulberry32(hashStr(seed)):Math.random;}

/* ======================== Tokenizer ========================= */
const KEYWORDS=new Set([
  'and','break','do','else','elseif','end','false','for','function',
  'if','in','local','nil','not','or','repeat','return','then','true',
  'until','while'
]);

function tokenize(src){
  const t=[];let i=0,n=src.length;
  const isWS=c=>c===' '||c==='\t'||c==='\r'||c==='\n';

  while(i<n){
    const c=src[i];

    if(isWS(c)){
      let j=i+1;while(j<n&&isWS(src[j]))j++;
      t.push({k:'ws',v:src.slice(i,j)});i=j;continue;
    }

    if(c==='-'&&src[i+1]==='-'){
      const lb=matchLongBracket(src,i+2);
      if(lb){
        const end=findLongClose(src,lb);
        if(end===-1)throw new Error('unterminated long comment');
        t.push({k:'comment',v:src.slice(i,end.end)});i=end.end;continue;
      }
      let j=i+2;while(j<n&&src[j]!=='\n')j++;
      t.push({k:'comment',v:src.slice(i,j)});i=j;continue;
    }

    if(c==='['){
      const lb=matchLongBracket(src,i);
      if(lb){
        const end=findLongClose(src,lb);
        if(end===-1)throw new Error('unterminated long string');
        t.push({k:'string',v:src.slice(i,end.end),long:true});i=end.end;continue;
      }
    }

    if(c==='"'||c==="'"){
      let j=i+1;
      while(j<n){
        if(src[j]==='\\'){j+=2;continue;}
        if(src[j]===c){j++;break;}
        if(src[j]==='\n')throw new Error('unterminated string');
        j++;
      }
      t.push({k:'string',v:src.slice(i,j)});i=j;continue;
    }

    if(/[0-9]/.test(c)||(c==='.'&&/[0-9]/.test(src[i+1]||''))){
      let j=i;
      if(c==='0'&&(src[i+1]==='x'||src[i+1]==='X')){
        j=i+2;while(j<n&&/[0-9a-fA-F]/.test(src[j]))j++;
      }else{
        while(j<n&&/[0-9.]/.test(src[j]))j++;
        if(src[j]==='e'||src[j]==='E'){
          j++;
          if(src[j]==='+'||src[j]==='-')j++;
          while(j<n&&/[0-9]/.test(src[j]))j++;
        }
      }
      t.push({k:'number',v:src.slice(i,j)});i=j;continue;
    }

    if(/[A-Za-z_]/.test(c)){
      let j=i+1;while(j<n&&/[A-Za-z0-9_]/.test(src[j]))j++;
      const w=src.slice(i,j);
      t.push({k:KEYWORDS.has(w)?'kw':'name',v:w});i=j;continue;
    }

    const three=src.substr(i,3);
    if(three==='...'){t.push({k:'op',v:'...'});i+=3;continue;}
    const two=src.substr(i,2);
    if(['==','~=','<=','>=','..','::'].includes(two)){t.push({k:'op',v:two});i+=2;continue;}
    t.push({k:'op',v:c});i++;
  }
  return t;
}
function matchLongBracket(src,i){
  if(src[i]!=='[')return null;
  let j=i+1,level=0;
  while(src[j]==='='){level++;j++;}
  if(src[j]!=='[')return null;
  return {level,bodyStart:j+1};
}
function findLongClose(src,lb){
  const close=']'+'='.repeat(lb.level)+']';
  const idx=src.indexOf(close,lb.bodyStart);
  return idx<0?-1:{end:idx+close.length};
}

/* ==================== Scope analysis ==================== */
function isSig(t){return t.k!=='ws'&&t.k!=='comment';}

function analyze(tokens){
  const sig=[];
  for(let i=0;i<tokens.length;i++) if(isSig(tokens[i])) sig.push({i,tok:tokens[i]});

  const blocks=[{id:0,start:-1,end:sig.length,type:'root'}];
  const stack=[blocks[0]];
  let idc=1;
  const decls=[];
  const peekV=(k,o=0)=>sig[k+o]?sig[k+o].tok.v:null;
  const peekK=(k,o=0)=>sig[k+o]?sig[k+o].tok.k:null;

  for(let k=0;k<sig.length;k++){
    const tok=sig[k].tok;
    if(tok.k!=='kw')continue;
    const kw=tok.v;

    if(kw==='function'){
      let p=k+1;while(p<sig.length&&sig[p].tok.v!=='(')p++;
      const params=[];let q=p+1;
      while(q<sig.length&&sig[q].tok.v!==')'){
        const pt=sig[q].tok;
        if(pt.k==='name')params.push(pt.v);
        q++;
      }
      const b={id:idc++,start:k,end:null,type:'fn',params};
      blocks.push(b);stack.push(b);
      for(const pn of params) decls.push({name:pn,blockId:b.id});
      continue;
    }
    if(kw==='if'||kw==='do'||kw==='while'||kw==='for'){
      const b={id:idc++,start:k,end:null,type:kw};
      blocks.push(b);stack.push(b);continue;
    }
    if(kw==='repeat'){
      const b={id:idc++,start:k+1,end:null,type:'repeat'};
      blocks.push(b);stack.push(b);continue;
    }
    if(kw==='end'||kw==='until'){
      const b=stack.pop();
      if(b&&b.id!==0)b.end=k;
      continue;
    }
    if(kw==='local'){
      const encl=stack[stack.length-1];
      if(peekV(k+1)==='function'&&peekK(k+2)==='name'){
        decls.push({name:peekV(k+2),blockId:encl.id});
        let p=k+3;while(p<sig.length&&sig[p].tok.v!=='(')p++;
        const params=[];let q=p+1;
        while(q<sig.length&&sig[q].tok.v!==')'){
          const pt=sig[q].tok;
          if(pt.k==='name')params.push(pt.v);
          q++;
        }
        const b={id:idc++,start:k+1,end:null,type:'fn',params};
        blocks.push(b);stack.push(b);
        for(const pn of params) decls.push({name:pn,blockId:b.id});
        continue;
      }
      let p=k+1;
      while(p<sig.length){
        const pt=sig[p].tok;
        if(pt.k!=='name')break;
        decls.push({name:pt.v,blockId:encl.id});
        p++;
        if(sig[p]&&sig[p].tok.v===','){p++;continue;}
        break;
      }
    }
  }
  while(stack.length>1){
    const b=stack.pop();
    if(b.end==null)b.end=sig.length;
  }

  const byId=new Map(blocks.map(b=>[b.id,b]));
  const scopes=decls.map(d=>{
    const b=byId.get(d.blockId)||blocks[0];
    return {name:d.name,start:b.start,end:b.end};
  });
  return {sig,scopes};
}

function resolveScope(scopes,name,at){
  let best=null;
  for(const s of scopes){
    if(s.name!==name)continue;
    if(at>=s.start&&at<=s.end){
      if(!best||(s.end-s.start)<(best.end-best.start))best=s;
    }
  }
  return best;
}

/* ================== Name generation ================== */
function genName(r,dontUse,used){
  const A='abcdefghijklmnopqrstuvwxyz';
  const B='ABCDEFGHIJKLMNOPQRSTUVWXYZ';
  const D='0123456789';
  for(;;){
    const len=5+Math.floor(r()*4);
    let s=A[Math.floor(r()*A.length)];
    for(let i=1;i<len;i++){
      const pool=i<2?A+D:B+A+D;
      s+=pool[Math.floor(r()*pool.length)];
    }
    if(KEYWORDS.has(s))continue;
    if(dontUse.has(s))continue;
    used.add(s);
    return s;
  }
}

/* ================== String encoding ================== */
function unescapeLua(s){
  let out='';let i=0;
  while(i<s.length){
    const c=s[i];
    if(c!=='\\'){out+=c;i++;continue;}
    i++;
    const e=s[i];
    if(e===undefined){out+='\\';break;}
    switch(e){
      case 'n':out+='\n';i++;break;
      case 't':out+='\t';i++;break;
      case 'r':out+='\r';i++;break;
      case 'a':out+='\x07';i++;break;
      case 'b':out+='\b';i++;break;
      case 'f':out+='\f';i++;break;
      case 'v':out+='\v';i++;break;
      case '\\':out+='\\';i++;break;
      case '"':out+='"';i++;break;
      case "'":out+="'";i++;break;
      case '\n':out+='\n';i++;break;
      case 'x':{
        const hex=s.substr(i+1,2);
        if(/^[0-9a-fA-F]{2}$/.test(hex)){
          out+=String.fromCharCode(parseInt(hex,16));i+=3;
        }else{out+='x';i++;}
        break;
      }
      case 'z':{
        i++;
        while(i<s.length&&/[ \t\r\n]/.test(s[i]))i++;
        break;
      }
      default:{
        if(/[0-9]/.test(e)){
          let d='';let j=i;
          while(j<s.length&&d.length<3&&/[0-9]/.test(s[j])){d+=s[j];j++;}
          out+=String.fromCharCode(parseInt(d,10));i=j;
        }else{out+=e;i++;}
      }
    }
  }
  return out;
}

function encString(r,lit){
  let content;
  if(lit.startsWith('[')){
    const m=lit.match(/^\[(=*)\[([\s\S]*)\]\1\]$/);
    if(!m)return null;
    content=m[2];
    if(content.startsWith('\r\n'))content=content.slice(2);
    else if(content.startsWith('\n')||content.startsWith('\r'))content=content.slice(1);
  }else{
    content=unescapeLua(lit.slice(1,-1));
  }
  if(content.length===0)return '""';
  const codes=[];
  for(let i=0;i<content.length;i++){
    const ch=content.charCodeAt(i);
    if(ch>255)return null;
    codes.push(ch);
  }
  const off=1+Math.floor(r()*200);
  const enc=codes.map(b=>b+off);
  return `(function(t,k)local s=""for i=1,#t do s=s..string.char(t[i]-k)end return s end)({${enc.join(',')}},${off})`;
}

/* ================== Number encoding ================== */
function encNumber(r,lit){
  const n=parseFloat(lit);
  if(!isFinite(n))return null;
  const a=Math.floor(r()*90000)+1000;
  const b=Math.floor(r()*90000)+1000;
  const c=a+b-n;
  return `(${a}+${b}-${Number(c)})`;
}

/* ================== Payload encoding (uppercase hex) ================== */
function lolEncode(str){
  let hex='';
  for(let i=0;i<str.length;i++){
    hex+=str.charCodeAt(i).toString(16).toUpperCase().padStart(2,'0');
  }
  let body='';
  for(let i=0;i<hex.length;i+=8){
    body+=hex.slice(i,i+8)+'Q';
  }
  return body;
}

/* ================== Junk injection ================== */
function junkConst(r){
  const a=100+Math.floor(r()*900);
  const b=1+Math.floor(r()*90);
  const c=1+Math.floor(r()*90);
  return `(${a}-(${b}+${c}))`;
}
function junkLine(r,varname){
  const target=junkConst(r);
  return `local ${varname}=0;while true do if ${varname}==0 then ${varname}=${target};break;end end;`;
}

/* ================== Fake decompiler prologue ================== */
function makeFakePrologue(r, usedNames){
  const L='abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ';
  const D='0123456789';
  const avoid=new Set(['B','C','S','T','L','P','D','s','f','e','w','i','o','l','n','c','a']);
  function pick(len){
    for(;;){
      const n=len||1;
      let s=L[Math.floor(r()*L.length)];
      for(let i=1;i<n;i++) s+=(r()<0.3?D:L)[Math.floor(r()*((r()<0.3?D:L).length))];
      if(avoid.has(s))continue;
      avoid.add(s);
      return s;
    }
  }
  const vByte = pick(1), vChar = pick(1), vSub = pick(1), vConcat = pick(1);
  const vInsert = pick(1), vLdexp = pick(1), vEnv = pick(1), vMT = pick(1);
  const vSel = pick(1), vUnpack = pick(1), vNum = pick(1), vFn = pick(1);
  const vArg = pick(1), vEmpty = pick(1), vRes = pick(1), vTbl = pick(1);
  const vIdx = pick(1), vInner = pick(1);

  const vBase = 256+Math.floor(r()*744);
  const vStart= 1+Math.floor(r()*40);
  const deadHex=(1000+Math.floor(r()*60000)).toString(16).toUpperCase();

  return `do local ${vByte}=string.byte;local ${vChar}=string.char;local ${vSub}=string.sub;local ${vConcat}=table.concat;local ${vInsert}=table.insert;local ${vLdexp}=math.ldexp;local ${vEnv}=getfenv or function()return _ENV end;local ${vMT}=setmetatable;local ${vSel}=select;local ${vUnpack}=unpack or table.unpack;local ${vNum}=tonumber;local function ${vFn}(${vArg})local ${vEmpty},${vRes},${vTbl}="","",{}local ${vIdx}=${vBase};local ${vInner}={}for ${vInner}=0,${vIdx}-1 do ${vTbl}[${vInner}]=${vChar}(${vInner})end;local ${vIdx}=${vStart};local function ${vInner}()local ${vEmpty}=${vNum}(${vSub}(${vArg},${vIdx},${vIdx}),36)${vIdx}=${vIdx}+1;local ${vRes}=${vNum}(${vSub}(${vArg},${vIdx},${vIdx}+${vEmpty}-1),36)${vIdx}=${vIdx}+${vEmpty};return ${vRes}end;${vEmpty}=${vChar}(${vInner}())${vTbl}[1]=${vEmpty};while ${vIdx}<#${vArg} do local ${vIdx}=${vInner}()if ${vTbl}[${vIdx}]then ${vRes}=${vTbl}[${vIdx}]else ${vRes}=${vEmpty}..${vSub}(${vEmpty},1,1)end;${vTbl}[${vIdx}]=${vEmpty}..${vSub}(${vRes},1,1)${vTbl}[#${vTbl}+1],${vEmpty},${vIdx}=${vRes},${vRes},${vIdx}+1 end;return ${vConcat}(${vTbl})end;if false then ${vFn}("${deadHex}") end;end;`;
}

/* ================== Smart-minify space rule ================== */
function needsSpace(prev,cur){
  if(!prev||!cur)return false;
  const pv=prev.v, cv=cur.v;
  if(!pv||!cv)return false;
  const last=pv[pv.length-1];
  const first=cv[0];
  const isWord=c=>/[A-Za-z0-9_]/.test(c);

  if(isWord(last)&&isWord(first))return true;
  if(prev.k==='number'&&pv.endsWith('.')&&first==='.')return true;
  if(prev.k==='number'&&first==='.')return true;
  if(last==='.'&&first==='.')return true;
  if(last==='-'&&first==='-')return true;
  return false;
}

/* ================== Anti-tamper guard ==================
 * Runs BEFORE the payload. If any check fires → print("dtc") and
 * abort (don't run payload).
 */
function makeGuard(r){
  const g = ()=>'g'+Math.floor(r()*1e9).toString(36);
  const dbg = g(), lstr = g(), h = g(), info = g(), env = g(), e2 = g();

  const check =
    `local ${dbg}=rawget(_G,"debug");` +
    `local ${lstr}=rawget(_G,"loadstring") or rawget(_G,"load");` +
    `local ${env}=rawget(_G,"getfenv");` +
    `if ${dbg} and type(${dbg}.gethook)=="function" then ` +
      `local ${h}=${dbg}.gethook();` +
      `if ${h}~=nil then print("dtc")return end ` +
    `end;` +
    `if ${lstr} and ${dbg} and type(${dbg}.getinfo)=="function" then ` +
      `local ${info}=${dbg}.getinfo(${lstr},"S");` +
      `if ${info} and ${info}.what=="Lua" then print("dtc")return end ` +
    `end;` +
    `if ${env} then local ${e2}=${env}(1);` +
      `if ${e2} and ${e2}~=_G then print("dtc")return end ` +
    `end;`;

  return `do ${check} end;`;
}

/* ================== Main obfuscate ================== */
function obfuscate(src,opts){
  opts=opts||{};
  const r=rng(opts.seed);

  let tokens=tokenize(src);
  const {sig,scopes}=analyze(tokens);

  const used=new Set();
  const dontUse=new Set();
  [
    'print','pairs','ipairs','require','pcall','select','tostring','tonumber',
    'type','string','table','math','io','os','loadstring','load','setmetatable',
    'getmetatable','rawget','rawset','error','assert','unpack','next','coroutine'
  ].forEach(n=>dontUse.add(n));

  const renameMap=new Map();
  for(const s of scopes) if(!renameMap.has(s)) renameMap.set(s,genName(r,dontUse,used));

  const newVal=new Array(tokens.length).fill(null);
  for(let k=0;k<sig.length;k++){
    const {i,tok}=sig[k];
    if(tok.k==='name'){
      const s=resolveScope(scopes,tok.v,k);
      if(s&&renameMap.has(s)) newVal[i]=renameMap.get(s);
    }else if(tok.k==='string'){
      if(opts.encryptStrings!==false){
        const e=encString(r,tok.v);
        if(e)newVal[i]=e;
      }
    }else if(tok.k==='number'){
      if(opts.encodeNumbers!==false){
        const e=encNumber(r,tok.v);
        if(e)newVal[i]=e;
      }
    }else if(tok.k==='comment'){
      if(opts.stripComments!==false) newVal[i]='';
    }
  }

  // ---- SMART MINIFY RECONSTRUCTION ----
  let out='';
  let last=null;

  for(let i=0;i<tokens.length;i++){
    const tok=tokens[i];
    if(tok.k==='ws') continue;
    if(tok.k==='comment'){
      if(opts.stripComments===false){
        const v=tok.v.replace(/[\r\n]+/g,' ');
        out+=v;
        last={k:'comment',v:v};
      }
      continue;
    }
    const val=newVal[i]!==null?newVal[i]:tok.v;
    if(last && needsSpace(last,tok)) out+=' ';
    out+=val;
    last=tok;
  }

  let finalSrc=out;

  if(opts.flatten!==false){
    const fv=genName(r,dontUse,used);
    finalSrc=
      `local ${fv}=0;while ${fv}==0 do ${fv}=1;if ${fv}==1 then break end end `+
      finalSrc;
  }

  if(opts.junk!==false){
    const jn=genName(r,dontUse,used);
    finalSrc=`do ${junkLine(r,jn)} end `+finalSrc;
  }

  if(opts.fakePrologue!==false){
    finalSrc=makeFakePrologue(r,used)+finalSrc;
  }

  // ---- Output path: IronBrew2 VM OR hex loader ----
  if(opts.vm && typeof IronVM!=='undefined'){
    finalSrc = IronVM.generate(finalSrc, r, {
      zeroWS: opts.zeroWS !== false,
      antiTamper: !!opts.antiTamper,
    });
  }else if(opts.loader!==false){
    const guardBlock = opts.antiTamper ? makeGuard(r) : '';
    finalSrc=makeLoader(finalSrc,r,opts.zeroWS!==false,guardBlock);
  }

  return {code:finalSrc};
}

/* ================== Loader wrapper ==================
 * Decompiler-style preamble aliases + fake base-36 decoder L(d)
 * that is never called, followed by the real hex payload decoder.
 * Payload is UPPERCASE hex wrapped in ('...') — no "LOL!" prefix.
 *
 * The tail contains a reference-style nested if/elseif VM-dispatch
 * chain. It is dead code inside `if false then ... end` within dummy
 * while-true blocks. Real execution is `return s(L(),{},r())()`.
 */
function makeLoader(src,r,zeroWS,guard){
  const encoded=lolEncode(src);
  const esc=encoded.replace(/\\/g,'\\\\').replace(/'/g,"\\'");

  const reserved=new Set(['L','P','D','w','s','f','e','n','o','l','t','c','h','i','a','K']);
  const L1='abcdefghijklmnopqrstuvwxyz';
  const used=new Set();
  function v(){
    for(;;){
      const n=1+Math.floor(r()*2);
      let s='';
      for(let i=0;i<n;i++)s+=L1[Math.floor(r()*L1.length)];
      if(reserved.has(s)||used.has(s))continue;
      used.add(s);return s;
    }
  }

  const V={
    byte:'d', char:'h', sub:'t', concat:'C', insert:'e',
    ldexp:'s', env:'r', mt:'A', sel:'E', unpack:'i', tonum:'f'
  };
  for(const k of Object.keys(V)){
    if(reserved.has(V[k])||used.has(V[k])) V[k]=v();
    used.add(V[k]);
  }
  const fnName='L';
  const fnArg='d';
  const fnLocal1='l';
  const fnLocal2='n';
  const fnLocal3='c';
  const fnBase=256;
  const fnLoopVar='e';
  const fnInner='a';

  const nv=v(), ov=v(), ev=v(), lv=v(), tv=v(), cv=v(), hv=v(), iv=v(), fv=v(), Kv=v(), av=v();

  const R = n => 1+Math.floor(r()*n);

  const opMove = () => `${nv}[${ev}[${R(40)}]]=${ev}[${R(40)}];${lv}=${lv}+1;${ev}=${ov}[${lv}];`;
  const opLoadK = () => `${nv}[${ev}[${R(40)}]]=${cv}[${ev}[${R(40)}]];${lv}=${lv}+1;${ev}=${ov}[${lv}];`;
  const opIndex = () => `${nv}[${ev}[${R(40)}]]=${nv}[${ev}[${R(40)}]][${ev}[${R(40)}]];${lv}=${lv}+1;${ev}=${ov}[${lv}];`;
  const opStore = () => `${nv}[${ev}[${R(40)}]][${ev}[${R(40)}]]=${nv}[${ev}[${R(40)}]];${lv}=${lv}+1;${ev}=${ov}[${lv}];`;
  const opBool = () => `${nv}[${ev}[${R(40)}]]=(${ev}[${R(40)}]~=0);${lv}=${lv}+1;${ev}=${ov}[${lv}];`;
  const opSub = () => `${nv}[${ev}[${R(40)}]]=${nv}[${ev}[${R(40)}]]-${nv}[${ev}[${R(40)}]];${lv}=${lv}+1;${ev}=${ov}[${lv}];`;
  const opCallV = () => {
    const t=v();
    return `${t}=${ev}[${R(40)}]${nv}[${t}]=${nv}[${t}](${iv}(${nv},${t}+1,${ev}[${R(40)}]))${lv}=${lv}+1;${ev}=${ov}[${lv}];`;
  };
  const opCall0 = () => {
    const t=v();
    return `${t}=${ev}[${R(40)}]${nv}[${t}](${nv}[${t}+1])${lv}=${lv}+1;${ev}=${ov}[${lv}];`;
  };
  const opCallNM = () => {
    const t=v();
    return `${t}=${ev}[${R(40)}]${nv}[${t}]=${nv}[${t}]()${lv}=${lv}+1;${ev}=${ov}[${lv}];`;
  };
  const opJmp = () => `if(${nv}[${ev}[${R(40)}]]<${ev}[${R(40)}])then ${lv}=${lv}+1;else ${lv}=${ev}[${R(40)}];end;`;
  const opTest = () => `if not ${nv}[${ev}[${R(40)}]]then ${lv}=${lv}+1;else ${lv}=${ev}[${R(40)}];end;`;
  const opFor = () => `for ${ev}=${ev}[${R(40)}],${ev}[${R(40)}]do ${nv}[${ev}]=nil;end;`;
  const opVararg = () => {
    const t=v(), c=v(), o=v();
    return `${t}=${ev}[${R(40)}];local ${c}=${ev}[${R(40)}];local ${o}=${t}+2;local ${t}={${nv}[${t}](${nv}[${t}+1],${nv}[${o}])};for ${ev}=1,${c} do ${nv}[${o}+${ev}]=${t}[${ev}];end;local ${t}=${t}[1]if ${t}then ${nv}[${o}]=${t} ${lv}=${ev}[${R(40)}];else ${lv}=${lv}+1;end;`;
  };
  const opMulti = () => {
    const t=v(), c=v();
    return `${t}=${ev}[${R(40)}];${c}=${nv}[${ev}[${R(40)}]];${nv}[${t}+1]=${c};${nv}[${t}]=${c}[${ev}[${R(40)}]];${lv}=${lv}+1;${ev}=${ov}[${lv}];`;
  };

  const gens=[opMove,opLoadK,opIndex,opStore,opBool,opSub,opCallV,opCall0,opCallNM,opJmp,opTest,opFor,opVararg,opMulti];

  function opsBlock(count){
    let s='';
    for(let i=0;i<count;i++) s+=gens[Math.floor(r()*gens.length)]();
    return s;
  }

  const base = 50 + Math.floor(r()*20);
  const t1 = base + Math.floor(r()*3);
  const t2 = t1 + 1 + Math.floor(r()*3);
  const t3 = t2 + 1 + Math.floor(r()*3);
  const inner21 = t2 - 2 + Math.floor(r()*2);

  function treeInner(threshold){
    return `if ${tv}<=${threshold} then if ${tv}==${threshold-1} then ${opsBlock(6+Math.floor(r()*4))}else ${opsBlock(2)}end;elseif ${tv}<=${threshold+1} then ${opsBlock(6+Math.floor(r()*4))}elseif ${tv}>${threshold+2} then ${opsBlock(6+Math.floor(r()*4))}else ${opsBlock(2)}end;`;
  }

  const d1='d', i1='i', c1='c', s1='s';
  const chain =
    `if ${tv}<=${t1} then ${treeInner(t1)}` +
    `elseif ${tv}>${t1+1} then ${lv}=${ev}[${R(40)}];` +
    `else ${nv}[${ev}[${R(40)}]]=${nv}[${ev}[${R(40)}]][${ev}[${R(40)}]];end;` +
    `elseif ${tv}<=${t2} then if ${tv}<=${inner21} then ${opsBlock(4)}` +
    `elseif ${tv}>${inner21+1} then ${opsBlock(4)}` +
    `else local ${d1}=${Kv}[${ev}[${R(40)}]];local ${i1};local ${c1}={};${i1}=${hv}({},{__index=function(${lv},${ev})local ${ev}=${c1}[${ev}];return ${ev}[1][${ev}[2]];end,__newindex=function(${nv},${ev},${lv})local ${ev}=${c1}[${ev}]${ev}[1][${ev}[2]]=${lv};end;});for ${s1}=1,${ev}[${R(40)}] do ${lv}=${lv}+1;local ${ev}=${ov}[${lv}];if ${ev}[1]==38 then ${c1}[${s1}-1]={${nv},${ev}[${R(40)}]};else ${c1}[${s1}-1]={${fv},${ev}[${R(40)}]};end;${av}[#${av}+1]=${c1};end;${nv}[${ev}[${R(40)}]]=${V.concat}(${d1},${i1},${s1});end;` +
    `elseif ${tv}<=${t3} then ${opsBlock(3)}` +
    `elseif ${tv}>${t3+1} then ${opsBlock(6+Math.floor(r()*4))}` +
    `else ${opsBlock(2)}end;`;

  const deadHex=(1000+Math.floor(r()*60000)).toString(16).toUpperCase();

  const preamble =
`local ${V.byte}=string.byte;local ${V.char}=string.char;local ${V.sub}=string.sub;local ${V.concat}=table.concat;local ${V.insert}=table.insert;local ${V.ldexp}=math.ldexp;local ${V.env}=getfenv or function()return _ENV end;local ${V.mt}=setmetatable;local ${V.sel}=select;local ${V.unpack}=unpack or table.unpack;local ${V.tonum}=tonumber;local function ${fnName}(${fnArg})local ${fnLocal1},${fnLocal2},${fnLocal3}="","",{}local o=${fnBase};local ${fnArg}={}for ${fnLoopVar}=0,o-1 do ${fnArg}[${fnLoopVar}]=${V.char}(${fnLoopVar})end;local ${fnLoopVar}=1;local function ${fnInner}()local ${fnLocal1}=${V.tonum}(${V.sub}(${fnArg},${fnLoopVar},${fnLoopVar}),36)${fnLoopVar}=${fnLoopVar}+1;local ${fnLocal2}=${V.tonum}(${V.sub}(${fnArg},${fnLoopVar},${fnLoopVar}+${fnLocal1}-1),36)${fnLoopVar}=${fnLoopVar}+${fnLocal1};return ${fnLocal2}end;${fnLocal1}=${V.char}(${fnInner}())${fnLocal3}[1]=${fnLocal1};while ${fnLoopVar}<#${fnArg} do local ${fnLoopVar}=${fnInner}()if ${fnArg}[${fnLoopVar}]then ${fnLocal2}=${fnArg}[${fnLoopVar}]else ${fnLocal2}=${fnLocal1}..${V.sub}(${fnLocal1},1,1)end;${fnArg}[o]=${fnLocal1}..${V.sub}(${fnLocal2},1,1)${fnLocal3}[#${fnLocal3}+1],${fnLocal1},o=${fnLocal2},${fnLocal2},o+1 end;return ${V.concat}(${fnLocal3})end;if false then ${fnName}("${deadHex}") end;`;

  const guardBlock = guard || '';

  const loader =
`local L=('${esc}') local P={} for w in ${V.sub}(L,1):gmatch("(.-)Q") do P[#P+1]=w end local D={} for _,w in ipairs(P) do for i=1,#w,2 do D[#D+1]=tonumber(${V.sub}(w,i,i+1),16) end end local s="" for i=1,#D do s=s..${V.char}(D[i]) end local f,e=loadstring(s) if not f then error(e or "load failed") end ${guardBlock} local ${nv},${ov},${Kv},${av}={},{},{},{} local ${ev},${lv},${tv}=${nv},0,1 do while true do while true do while true do while true do if false then ${lv}=${lv}+1;${ev}=${ov}[${lv}];${chain}${ev}=${ov}[${lv}];${nv}[${ev}[${R(40)}]]=${ev}[${R(40)}];elseif ${tv}>53 then ${lv}=${ev}[${R(40)}];else ${nv}[${ev}[${R(40)}]]=${nv}[${ev}[${R(40)}]][${ev}[${R(40)}]];end;end;end;end;l=l+1;end;end;end;local s=function(a,b,c)return function(...)return f(...)end end;local L=function()return nil end;local r=function()return nil end;return s(L(),{},r())()`;

  return preamble + loader;
}

/* ================== Exports ================== */
global.LuaObfuscator={
  obfuscate,
  tokenize,
  lolEncode,
  unescapeLua,
  needsSpace,
  genName,
  makeGuard,
};
})(typeof window!=='undefined'?window:this);
