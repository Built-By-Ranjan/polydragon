'use strict';
// ═══════════════════════════════════════════════════════════════
//  POLY ARENA — SINGLE PLAYER (Bot Duel → Dragon)
//  Based on bhittu21/polygame (MIT). Multiplayer/socket code removed;
//  bot AI, difficulty levels, fireball-throwing dragon and a short
//  3-4 minute match flow added.
// ═══════════════════════════════════════════════════════════════

/* ─── CONFIG ─────────────────────────────────────────────────── */
const MOVE_SPEED    = 9.5;
const SPRINT_MULT   = 2.0;
const PLAYER_HEIGHT = 1.7;
const BODY_Y        = 1.0;
const NORMAL_FOV    = 75;
const NET_RATE_MS   = 45;
const MAP_HALF      = 29;
const GRAVITY       = 22;
const JUMP_FORCE    = 8.5;

const WEAPONS = [
  { id:'rifle',  name:'AUTO RIFLE',   damage:20,  headDmg:20,  fireRate:110,  auto:true,  scopeFOV:52, spread:0.003  },
  { id:'sniper', name:'SNIPER RIFLE', damage:95,  headDmg:100, fireRate:1600, auto:false, scopeFOV:12, spread:0.0002 },
];

/* ─── GLOBALS ────────────────────────────────────────────────── */
let scene, camera, renderer;
let ambientLight, sunLight;
let myId, myName;
let myHealth = 100, alive = true, gameStarted = false;
let pointerLocked = false;

let weaponIdx       = 0;
const gunGroups     = [];
const muzzleFlashes = [];

const otherPlayers  = {};   // id → { group }

const keys   = {};
const mouse  = { left:false, right:false, _wasLeft:false };
let yaw = 0, pitch = 0;
// Sensitivity: level 1..30 (menu slider, or [ ] keys in game). level 8 = 0.0010 rad/count (~0.057 deg).
// Old game used a fixed 0.0022 (~0.126 deg/count) = way too fast. Scoped sensitivity now scales with FOV.
let sensLevel = 8;
const SENS_PER_LEVEL = 0.000125;
const TAN_NORMAL = Math.tan(NORMAL_FOV*Math.PI/360);
let sensitivity = sensLevel*SENS_PER_LEVEL;
const PITCH_MAX = 1.45;

let currentFOV = NORMAL_FOV;
let targetFOV  = NORMAL_FOV;

// Physics
let velocityY   = 0;
let onGround    = true;
let jumpPressed = false;

let lastTime = 0, lastShot = 0, lastMoveSent = 0;
let gunBobT = 0, footstepTimer = 0;
let muzzleTimer;

const wallMeshes = [];
const colliders  = [];

/* ─── DRAGON ─────────────────────────────────────────────────── */
let dragonGroup    = null;
let dragonData     = null;   // { startAngle, clientStartTime, health, maxHealth }
const dragonHitMeshes = [];  // meshes players can shoot

// tiny DOM helpers: only touch the DOM when the value really changed (saves FPS)
const _dom={};
function $(id){ return _dom[id]||(_dom[id]=document.getElementById(id)); }
function setDisp(id,v){ const e=$(id); if(e&&e._d!==v){ e.style.display=v; e._d=v; } }
function setTxt(id,t){ const e=$(id); if(e&&e._t!==t){ e.textContent=t; e._t=t; } }

const ENV_NORMAL = { fogR:0x7a/255,fogG:0xb4/255,fogB:0xcc/255, ambR:1.0,ambG:.93,ambB:.87, sunR:1,sunG:1,sunB:1, sunInt:1.0, fogNear:40, fogFar:130 };
const ENV_DRAGON = { fogR:.26,fogG:.03,fogB:.02, ambR:.62,ambG:.22,ambB:.17, sunR:1,sunG:.5,sunB:.2, sunInt:.6, fogNear:35, fogFar:130 };
let envT = 0;
const _envCol = new THREE.Color();
const SKY_NIGHT = {r:.35,g:.034,b:.022};   // multiplies the sky texture: horizon ~= fog colour, zenith ~black-red

/* ─── AUDIO ──────────────────────────────────────────────────── */
let audioCtx = null;
function getAudio(){
  if(!audioCtx) audioCtx=new (window.AudioContext||window.webkitAudioContext)();
  if(audioCtx.state==='suspended') audioCtx.resume();
  return audioCtx;
}
function _noiseBurst(ctx,freq,dur,vol,q=0.45){
  try{
    const n=Math.floor(ctx.sampleRate*dur);
    const buf=ctx.createBuffer(1,n,ctx.sampleRate);
    const d=buf.getChannelData(0);
    for(let i=0;i<n;i++) d[i]=(Math.random()*2-1)*Math.exp(-i/(n*0.1));
    const src=ctx.createBufferSource(); src.buffer=buf;
    const bp=ctx.createBiquadFilter(); bp.type='bandpass'; bp.frequency.value=freq; bp.Q.value=q;
    const g=ctx.createGain();
    g.gain.setValueAtTime(vol,ctx.currentTime);
    g.gain.exponentialRampToValueAtTime(0.001,ctx.currentTime+dur);
    src.connect(bp); bp.connect(g); g.connect(ctx.destination);
    src.start();
  }catch(e){}
}
function _oscBurst(ctx,f0,f1,dur,vol,type='sine'){
  try{
    const t=ctx.currentTime;
    const osc=ctx.createOscillator(); const g=ctx.createGain();
    osc.type=type;
    osc.frequency.setValueAtTime(f0,t);
    osc.frequency.exponentialRampToValueAtTime(f1,t+dur);
    g.gain.setValueAtTime(vol,t);
    g.gain.exponentialRampToValueAtTime(0.001,t+dur);
    osc.connect(g); g.connect(ctx.destination);
    osc.start(); osc.stop(t+dur);
  }catch(e){}
}
function playRifleShot(){  try{ const c=getAudio(); _noiseBurst(c,900,.08,.6,.4); _oscBurst(c,130,40,.09,.35); }catch(e){} }
function playSniperShot(){ try{ const c=getAudio(); _noiseBurst(c,380,.22,1.0,.28); _oscBurst(c,90,20,.35,.25,'sawtooth'); setTimeout(()=>{ try{ _noiseBurst(c,280,.12,.18,.2); }catch(e){} },130); }catch(e){} }
function playHitSound(){   try{ const c=getAudio(); _oscBurst(c,900,440,.09,.28); }catch(e){} }
function playWeaponSwitch(){ try{ const c=getAudio();const t=c.currentTime;const osc=c.createOscillator();const g=c.createGain();osc.type='square';osc.frequency.setValueAtTime(200,t);osc.frequency.setValueAtTime(320,t+.05);g.gain.setValueAtTime(.12,t);g.gain.exponentialRampToValueAtTime(.001,t+.12);osc.connect(g);g.connect(c.destination);osc.start();osc.stop(t+.12); }catch(e){} }
function playFootstep(){   try{ const c=getAudio(); _noiseBurst(c,140,.04,.07,2.2); }catch(e){} }
function playJump(){       try{ const c=getAudio(); _oscBurst(c,180,320,.12,.12); }catch(e){} }
function playDragonRoar(){
  try{
    const c=getAudio();
    [0,.4,.9].forEach((delay,i)=>{
      const t=c.currentTime+delay;
      const osc=c.createOscillator(); const g=c.createGain();
      osc.type='sawtooth';
      osc.frequency.setValueAtTime(28+i*12,t);
      osc.frequency.exponentialRampToValueAtTime(55+i*18,t+.35);
      osc.frequency.exponentialRampToValueAtTime(22,t+1.2);
      g.gain.setValueAtTime(0,t);
      g.gain.linearRampToValueAtTime(.22,t+.2);
      g.gain.exponentialRampToValueAtTime(.001,t+1.3);
      osc.connect(g); g.connect(c.destination);
      osc.start(t); osc.stop(t+1.4);
    });
  }catch(e){}
}

/* ─── ENTRY ──────────────────────────────────────────────────── */
function startGame(){
  const nameEl=document.getElementById('name-inp');
  myName=(nameEl.value.trim()||'Ghost'+Math.floor(Math.random()*9999)).substring(0,16);
  setDifficulty(window.selectedDiff||'medium');

  document.getElementById('overlay').style.display='none';
  document.getElementById('lock-msg').style.display='block';
  // stop the menu's space-background animation (it kept redrawing every frame behind the game = big FPS loss)
  window.__bgStopped=true;
  const bgc=document.getElementById('bg-canvas'); if(bgc) bgc.style.display='none';
  document.body.classList.add('ingame');
  sensLevel=clamp(window.mouseSensLevel||8,1,30);

  initRenderer();
  buildMap();
  buildGuns();
  initInput();
  initLocalGame();

  lockPointer();

  gameStarted=true;
  lastTime=performance.now();
  requestAnimationFrame(gameLoop);
}

/* raw (unaccelerated) mouse input when the browser supports it -> consistent aim */
function lockPointer(){
  const c=document.getElementById('game-canvas');
  try{
    const p=c.requestPointerLock({unadjustedMovement:true});
    if(p&&p.catch) p.catch(()=>{ try{ c.requestPointerLock(); }catch(e){} });
  }catch(e){ try{ c.requestPointerLock(); }catch(e2){} }
}

/* ─── RENDERER ───────────────────────────────────────────────── */
function initRenderer(){
  const canvas=document.getElementById('game-canvas');
  renderer=new THREE.WebGLRenderer({canvas,antialias:false,powerPreference:'high-performance'});
  renderer.setPixelRatio(Math.min(devicePixelRatio,1.5));
  renderer.setSize(innerWidth,innerHeight);
  renderer.setClearColor(0x7ab4cc);

  scene=new THREE.Scene();
  scene.fog=new THREE.Fog(0x7ab4cc,40,130);

  camera=new THREE.PerspectiveCamera(NORMAL_FOV,innerWidth/innerHeight,0.05,400);
  camera.position.set(0,PLAYER_HEIGHT,0);
  scene.add(camera);

  ambientLight=new THREE.AmbientLight(0xffeedd,.6); scene.add(ambientLight);
  sunLight=new THREE.DirectionalLight(0xffffff,1.0); sunLight.position.set(50,80,40); scene.add(sunLight);
  const fill=new THREE.DirectionalLight(0x8899ff,.28); fill.position.set(-30,15,-30); scene.add(fill);

  addEventListener('resize',()=>{
    camera.aspect=innerWidth/innerHeight;
    camera.updateProjectionMatrix();
    renderer.setSize(innerWidth,innerHeight);
  });
}

/* ─── HELPERS ────────────────────────────────────────────────── */
function mat(color){ return new THREE.MeshLambertMaterial({color,flatShading:true}); }
function box(w,h,d,c,x,y,z,solid=false){
  const m=new THREE.Mesh(new THREE.BoxGeometry(w,h,d),mat(c));
  m.position.set(x,y,z); scene.add(m);
  if(solid) wallMeshes.push(m);
  return m;
}
function mobj(geo,material,x,y,z){ const m=new THREE.Mesh(geo,material); m.position.set(x,y,z); return m; }
function clamp(v,lo,hi){ return v<lo?lo:v>hi?hi:v; }
function esc(s){ return String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;'); }
function lerpHex(a,b,t){
  const ar=(a>>16)&255,ag=(a>>8)&255,ab=a&255;
  const br=(b>>16)&255,bg=(b>>8)&255,bb=b&255;
  return (Math.round(ar+(br-ar)*t)<<16)|(Math.round(ag+(bg-ag)*t)<<8)|Math.round(ab+(bb-ab)*t);
}

/* ─── TEXTURES (generated, no external files) ─────────────────── */
function makeCanvasTex(w,h,draw,rx,ry){
  const c=document.createElement('canvas'); c.width=w; c.height=h;
  draw(c.getContext('2d'),w,h);
  const t=new THREE.CanvasTexture(c);
  t.wrapS=t.wrapT=THREE.RepeatWrapping; t.repeat.set(rx||1,ry||1);
  t.magFilter=THREE.NearestFilter;
  return t;
}
let skyMat=null, sunMesh=null, cloudGroup=null, skyRig=null;
const cloudMats=[];

/* ─── MAP ────────────────────────────────────────────────────── */
function addCollider(cx,cz,w,d,pad=0.45){
  colliders.push({minX:cx-w/2-pad,maxX:cx+w/2+pad,minZ:cz-d/2-pad,maxZ:cz+d/2+pad});
}
function decor(geo,color,x,y,z,basic){
  const m=new THREE.Mesh(geo,basic?new THREE.MeshBasicMaterial({color}):mat(color));
  m.position.set(x,y,z); scene.add(m); return m;
}

function buildMap(){
  /* outside ground (flat inside arena, bumpy outside) */
  const gGeo=new THREE.PlaneGeometry(160,160,32,32);
  const gPos=gGeo.attributes.position;
  for(let i=0;i<gPos.count;i++){
    const vx=gPos.getX(i),vy=gPos.getY(i);
    if(Math.max(Math.abs(vx),Math.abs(vy))>MAP_HALF+6 && Math.min(80-Math.abs(vx),80-Math.abs(vy))>10)
      gPos.setZ(i,(Math.random()-.5)*.5);
  }
  gGeo.computeVertexNormals();
  const gnd=new THREE.Mesh(gGeo,mat(0x4f8434)); gnd.rotation.x=-Math.PI/2; gnd.position.y=-.03; scene.add(gnd);

  /* arena floor: concrete tiles */
  const floorTex=makeCanvasTex(128,128,(g,w,h)=>{
    g.fillStyle='#7b7f84'; g.fillRect(0,0,w,h);
    for(let i=0;i<500;i++){ const v=110+Math.random()*40|0; g.fillStyle=`rgb(${v},${v+3},${v+6})`; g.fillRect(Math.random()*w,Math.random()*h,2,2); }
    g.strokeStyle='#5a5e63'; g.lineWidth=3; g.strokeRect(0,0,w,h);
    g.strokeStyle='rgba(255,255,255,.07)'; g.lineWidth=1; g.strokeRect(4,4,w-8,h-8);
  },MAP_HALF*2/4,MAP_HALF*2/4);
  const floor=new THREE.Mesh(new THREE.PlaneGeometry(MAP_HALF*2,MAP_HALF*2),
    new THREE.MeshLambertMaterial({map:floorTex}));
  floor.rotation.x=-Math.PI/2; floor.position.y=.02; scene.add(floor);

  /* painted markings */
  const paint=0xd9c25a;
  const ring=new THREE.Mesh(new THREE.RingGeometry(5.4,5.7,48),new THREE.MeshBasicMaterial({color:paint,side:THREE.DoubleSide}));
  ring.rotation.x=-Math.PI/2; ring.position.y=.04; scene.add(ring);
  [[0,0,.35,MAP_HALF*2-4],[0,0,MAP_HALF*2-4,.35]].forEach(([x,z,w,d])=>{
    const l=decor(new THREE.BoxGeometry(w,.02,d),0x9a9a8a,x,.035,z,true); l.material.transparent=true; l.material.opacity=.5;
  });
  [[-15,-15,0x44ddff],[15,15,0xff4455]].forEach(([x,z,c])=>{
    const r=new THREE.Mesh(new THREE.RingGeometry(1.3,1.7,24),new THREE.MeshBasicMaterial({color:c,side:THREE.DoubleSide}));
    r.rotation.x=-Math.PI/2; r.position.set(x,.05,z); scene.add(r);
  });

  /* perimeter walls with trim + battlements */
  const WH=5.5,WL=MAP_HALF*2;
  const wallCol=0x8f7d62, trimCol=0x6b5c47;
  [[WL+2,WH,1.2,0,MAP_HALF],[WL+2,WH,1.2,0,-MAP_HALF],[1.2,WH,WL+2,-MAP_HALF,0],[1.2,WH,WL+2,MAP_HALF,0]]
  .forEach(([w,h,d,x,z])=>{
    box(w,h,d,wallCol,x,h/2,z,true);
    decor(new THREE.BoxGeometry(w>d?w+.3:1.6,.9,w>d?1.6:d+.3),trimCol,x,.45,z);
  });
  addCollider(0,MAP_HALF,WL,1.2,.7); addCollider(0,-MAP_HALF,WL,1.2,.7);
  addCollider(-MAP_HALF,0,1.2,WL,.7); addCollider(MAP_HALF,0,1.2,WL,.7);
  for(let i=-28;i<=28;i+=3.6){
    [[i,MAP_HALF],[i,-MAP_HALF],[MAP_HALF,i],[-MAP_HALF,i]].forEach(([x,z])=>
      decor(new THREE.BoxGeometry(1.5,.9,1.5),trimCol,x,WH+.45,z));
  }
  /* banners on the inner faces of north/south walls */
  [-18,0,18].forEach((x,i)=>{
    [[MAP_HALF-.65,Math.PI],[-MAP_HALF+.65,0]].forEach(([z,ry])=>{
      const col=(i%2===0)?0xb02a2a:0x1f7a8c;
      const f=new THREE.Mesh(new THREE.PlaneGeometry(1.7,3.2),new THREE.MeshBasicMaterial({color:col,side:THREE.DoubleSide}));
      f.position.set(x,3.1,z); f.rotation.y=ry; scene.add(f);
      const s=new THREE.Mesh(new THREE.PlaneGeometry(1.7,.25),new THREE.MeshBasicMaterial({color:0xe8c24a,side:THREE.DoubleSide}));
      s.position.set(x,4.3,z+(ry?-.01:.01)); s.rotation.y=ry; scene.add(s);
    });
  });

  /* corner towers */
  [[-25.5,-25.5],[25.5,-25.5],[-25.5,25.5],[25.5,25.5]].forEach(([x,z])=>{
    box(5,9,5,0x9a8870,x,4.5,z,true); addCollider(x,z,5,5);
    decor(new THREE.BoxGeometry(5.8,.7,5.8),trimCol,x,9.35,z);
    const roof=decor(new THREE.ConeGeometry(4.2,2.8,4),0x8a3b2a,x,11.1,z); roof.rotation.y=Math.PI/4;
    decor(new THREE.BoxGeometry(1.2,1.6,.2),0x222a30,x+(x>0?-2.52:2.52),6.2,z); // dark window slit
  });

  /* central bunker (open to the south) */
  const stone=0x8a7a9a;
  box(1,3.5,8,stone,4.5,1.75,0,true);  addCollider(4.5,0,1,8);
  box(1,3.5,8,stone,-4.5,1.75,0,true); addCollider(-4.5,0,1,8);
  box(8,3.5,1,stone,0,1.75,4,true);    addCollider(0,4,8,1);
  [[-4.5,-4],[4.5,-4],[-4.5,4],[4.5,4]].forEach(([x,z])=>decor(new THREE.BoxGeometry(1.5,4.1,1.5),0x6f6280,x,2.05,z));

  /* low concrete barriers */
  const conc=0x9a8870;
  [[0,14,9,1],[0,-14,9,1],[14,0,1,9],[-14,0,1,9]].forEach(([x,z,w,d])=>{
    box(w,2.2,d,conc,x,1.1,z,true); addCollider(x,z,w,d);
    decor(new THREE.BoxGeometry(w+.15,.2,d+.15),0x6d5f4e,x,2.3,z);
  });
  [[23,0,1,7],[-23,0,1,7],[0,23,7,1],[0,-23,7,1]].forEach(([x,z,w,d])=>{
    box(w,2.2,d,0x7a6a5a,x,1.1,z,true); addCollider(x,z,w,d);
  });
  [[11,-22,2.5,1],[-11,22,2.5,1],[22,11,1,2.5],[-22,-11,1,2.5]].forEach(([x,z,w,d])=>{
    box(w,1.5,d,0x6a7a4a,x,.75,z,true); addCollider(x,z,w,d);
  });

  /* wooden crates (textured), some stacked */
  const crateTex=makeCanvasTex(64,64,(g,w,h)=>{
    g.fillStyle='#a9753a'; g.fillRect(0,0,w,h);
    g.fillStyle='#8a5a28'; for(let y=0;y<h;y+=16) g.fillRect(0,y,w,2);
    g.strokeStyle='#5a3a18'; g.lineWidth=5; g.strokeRect(2,2,w-4,h-4);
    g.beginPath(); g.moveTo(4,4); g.lineTo(w-4,h-4); g.moveTo(w-4,4); g.lineTo(4,h-4); g.stroke();
  });
  const crateMat=(tint)=>new THREE.MeshLambertMaterial({map:crateTex,color:tint});
  function crate(x,z,s,tint,stack){
    const m=new THREE.Mesh(new THREE.BoxGeometry(s,s,s),crateMat(tint)); m.position.set(x,s/2,z);
    scene.add(m); wallMeshes.push(m); addCollider(x,z,s,s);
    if(stack){
      const t=new THREE.Mesh(new THREE.BoxGeometry(s*.8,s*.8,s*.8),crateMat(tint));
      t.position.set(x+s*.05,s+s*.4,z); t.rotation.y=.35; scene.add(t); wallMeshes.push(t);
    }
  }
  crate(9,9,1.9,0xffffff,true); crate(-9,9,1.9,0xe8d8c0,false);
  crate(9,-9,1.9,0xe8d8c0,false); crate(-9,-9,1.9,0xffffff,true);
  crate(-19,15,1.6,0xffffff,false); crate(-17.2,15.3,1.6,0xe8d8c0,true);
  crate(19,-15,1.6,0xffffff,false); crate(17.2,-15.3,1.6,0xe8d8c0,true);

  /* barrels */
  function barrel(x,z,col){
    const b=new THREE.Mesh(new THREE.CylinderGeometry(.55,.55,1.4,10),mat(col));
    b.position.set(x,.7,z); scene.add(b); wallMeshes.push(b); addCollider(x,z,1.1,1.1);
    [.3,1.1].forEach(y=>decor(new THREE.CylinderGeometry(.58,.58,.1,10),0x2a2a2a,x,y,z));
  }
  [[-20,-8,0xb83a2a],[-21.2,-6.9,0xb83a2a],[-19.4,-6.6,0x3a6aa8],
   [20,8,0xb83a2a],[21.2,6.9,0xc9a020],[19.4,6.6,0xb83a2a],
   [-8,20,0x3a6aa8],[-6.8,21.2,0xb83a2a],[8,-20,0xc9a020],[6.8,-21.2,0x3a6aa8]].forEach(([x,z,c])=>barrel(x,z,c));

  /* sandbag walls */
  function sandbags(x,z,len,alongX){
    const n=Math.round(len/.9);
    for(let row=0;row<2;row++)for(let i=0;i<n;i++){
      const off=(i-(n-1)/2)*.9+(row?.45:0);
      const c=lerpHex(0xb9a56a,0xa08c52,Math.random());
      const bag=new THREE.Mesh(new THREE.BoxGeometry(alongX?.85:.55,.42,alongX?.55:.85),mat(c));
      bag.position.set(x+(alongX?off:0),.21+row*.42,z+(alongX?0:off));
      scene.add(bag); wallMeshes.push(bag);
    }
    addCollider(x,z,alongX?len:.6,alongX?.6:len);
  }
  sandbags(-6,-20,4.5,true); sandbags(6,20,4.5,true);
  sandbags(-20,2,3.6,false); sandbags(20,-2,3.6,false);

  /* lamp posts */
  [[-18,0],[18,0],[0,-18],[0,18]].forEach(([x,z])=>{
    decor(new THREE.CylinderGeometry(.1,.14,5,6),0x2a2d31,x,2.5,z);
    decor(new THREE.BoxGeometry(.7,.12,.12),0x2a2d31,x,5,z);
    decor(new THREE.SphereGeometry(.28,8,6),0xfff2a0,x,4.75,z,true);
    const gl=decor(new THREE.SphereGeometry(.6,8,6),0xffe680,x,4.75,z,true); gl.material.transparent=true; gl.material.opacity=.22;
    addCollider(x,z,.3,.3,.3);
  });

  /* trees & rocks outside */
  [[38,8],[38,-12],[38,28],[38,-28],[-38,8],[-38,-18],[-38,28],
   [12,38],[-10,38],[26,38],[10,-38],[-14,-38],[24,-38],[34,-4],[-34,16],[-6,34]].forEach(([x,z])=>placeTree(x,z));
  for(let i=0;i<14;i++){
    const a=Math.random()*Math.PI*2,r=36+Math.random()*30,s=.8+Math.random()*1.6;
    const rk=decor(new THREE.DodecahedronGeometry(s,0),lerpHex(0x6b6b66,0x8a8a82,Math.random()),Math.cos(a)*r,s*.45,Math.sin(a)*r);
    rk.rotation.set(Math.random(),Math.random(),Math.random());
  }

  /* mountains (visible through light fog) */
  for(let i=0;i<12;i++){
    const a=(i/12)*Math.PI*2+.3,r=96+Math.random()*14;
    const mh=20+Math.random()*20,mw=14+Math.random()*14;
    const m=new THREE.Mesh(new THREE.ConeGeometry(mw/2,mh,5+Math.floor(Math.random()*3)),
      mat(lerpHex(0x3a5a48,0x6a8a78,Math.random())));
    m.position.set(Math.cos(a)*r,mh/2-3,Math.sin(a)*r);
    m.rotation.y=Math.random()*Math.PI; scene.add(m);
    if(mh>28){ const cap=new THREE.Mesh(new THREE.ConeGeometry(mw*.17,mh*.26,5),mat(0xf2f6fa));
      cap.position.set(m.position.x,mh-3-mh*.13,m.position.z); scene.add(cap); }
  }

  /* sky gradient + sun + clouds
     BUG FIX: all of this now lives in skyRig which follows the camera every frame.
     Before, the sky sphere stayed at the world origin, so when the player walked away from the centre
     the far side of the sphere went past the camera far-plane and got clipped -> a big hole showing the
     clear colour. In daytime it was invisible (clear colour ~ horizon blue); at dragon-night it was a
     big red hexagon with nothing in it (the "blind spot"). */
  skyRig=new THREE.Group(); scene.add(skyRig);
  const skyTex=makeCanvasTex(8,256,(g,w,h)=>{
    const gr=g.createLinearGradient(0,0,0,h);
    gr.addColorStop(0,'#2e6fb8'); gr.addColorStop(.5,'#6fb0dc'); gr.addColorStop(1,'#bfe0ea');
    g.fillStyle=gr; g.fillRect(0,0,w,h);
  });
  skyTex.magFilter=THREE.LinearFilter;
  skyMat=new THREE.MeshBasicMaterial({map:skyTex,side:THREE.BackSide,fog:false,depthWrite:false});
  const sky=new THREE.Mesh(new THREE.SphereGeometry(150,24,16),skyMat); sky.renderOrder=-10; skyRig.add(sky);
  sunMesh=new THREE.Mesh(new THREE.SphereGeometry(7,12,8),new THREE.MeshBasicMaterial({color:0xfff3c4,fog:false}));
  sunMesh.position.set(50,80,40).normalize().multiplyScalar(135); skyRig.add(sunMesh);
  const halo=new THREE.Mesh(new THREE.SphereGeometry(13,12,8),new THREE.MeshBasicMaterial({color:0xffe9a0,transparent:true,opacity:.2,fog:false}));
  sunMesh.add(halo);
  cloudGroup=new THREE.Group();
  for(let i=0;i<10;i++){
    const c=new THREE.Group(),a=Math.random()*Math.PI*2,r=95+Math.random()*40;
    for(let k=0;k<4;k++){
      const cm=new THREE.MeshBasicMaterial({color:0xffffff,transparent:true,opacity:.75,fog:false});
      cloudMats.push(cm);
      const p=new THREE.Mesh(new THREE.BoxGeometry(10+Math.random()*10,3+Math.random()*2,6+Math.random()*4),cm);
      p.position.set(k*7-10,Math.random()*2,Math.random()*4-2); c.add(p);
    }
    c.position.set(Math.cos(a)*r,78+Math.random()*25,Math.sin(a)*r); c.rotation.y=-a; cloudGroup.add(c);
  }
  skyRig.add(cloudGroup);

  /* static map objects never move -> freeze their matrices (less CPU per frame) */
  for(const ch of scene.children){
    if(ch===skyRig||ch===camera||ch.isLight) continue;
    ch.traverse(o=>{ o.updateMatrix(); o.matrixAutoUpdate=false; });
  }
}

function placeTree(x,z){
  const h=1.4+Math.random()*.9;
  const trunk=new THREE.Mesh(new THREE.CylinderGeometry(.1,.2,h,5),mat(0x6a4022));
  trunk.position.set(x,h/2,z);
  scene.add(trunk);
  for(let k=0;k<3;k++){
    const lw=1.5-k*.35+Math.random()*.2,lh=1.7+Math.random()*.5;
    const leaves=new THREE.Mesh(new THREE.ConeGeometry(lw,lh,6),mat(lerpHex(0x2a5f20,0x3f8a2e,Math.random())));
    leaves.position.set(x,h+k*1.0+lh/2-.2,z); scene.add(leaves);
  }
}

/* ─── LOCAL GUN MODELS ───────────────────────────────────────── */
let gunKick=0, gunBlend=0, gunMoving=false, gunSprint=false;
let flashTex=null;

function getFlashTex(){
  if(flashTex) return flashTex;
  const c=document.createElement('canvas'); c.width=c.height=64;
  const g=c.getContext('2d');
  const gr=g.createRadialGradient(32,32,2,32,32,30);
  gr.addColorStop(0,'rgba(255,255,230,1)'); gr.addColorStop(.35,'rgba(255,200,60,.9)'); gr.addColorStop(1,'rgba(255,120,0,0)');
  g.fillStyle=gr; g.fillRect(0,0,64,64);
  g.fillStyle='rgba(255,230,140,.95)';
  for(let i=0;i<4;i++){ g.save(); g.translate(32,32); g.rotate(i*Math.PI/4); g.fillRect(-30,-2,60,4); g.restore(); }
  flashTex=new THREE.CanvasTexture(c);
  return flashTex;
}
function makeMuzzleFlash(size){
  const m=new THREE.MeshBasicMaterial({map:getFlashTex(),transparent:true,opacity:0,depthTest:false,side:THREE.DoubleSide});
  const a=new THREE.Mesh(new THREE.PlaneGeometry(size,size),m);
  const b=new THREE.Mesh(new THREE.PlaneGeometry(size,size),m);
  b.rotation.y=Math.PI/2; a.add(b);
  a.rotation.y=Math.PI/2;   // facing sideways like a flash
  return a;
}

function gbox(g,w,h,d,color,x,y,z,rx){
  const m=mobj(new THREE.BoxGeometry(w,h,d),typeof color==='number'?mat(color):color,x,y,z);
  if(rx) m.rotation.x=rx; g.add(m); return m;
}
function gcyl(g,r,len,color,x,y,z){
  const geo=new THREE.CylinderGeometry(r,r,len,10); geo.rotateX(Math.PI/2);
  const m=mobj(geo,typeof color==='number'?mat(color):color,x,y,z); g.add(m); return m;
}
// arm/forearm box between two points (group must be at identity while building)
function glimb(g,from,to,w,color){
  const a=new THREE.Vector3(...from),b=new THREE.Vector3(...to);
  const len=a.distanceTo(b);
  const m=mobj(new THREE.BoxGeometry(w,w,len),mat(color),(a.x+b.x)/2,(a.y+b.y)/2,(a.z+b.z)/2);
  g.add(m); m.lookAt(b); return m;
}

function buildGuns(){ buildRifle(); buildSniper(); }

function buildRifle(){
  const g=new THREE.Group();
  const body=0x4a4e55, dark=0x24262b, olive=0x5a6140, skin=0xd9a98a, sleeve=0x2f4f3f;
  gbox(g,.07,.09,.32,body,0,0,0);                 // receiver
  gbox(g,.045,.02,.34,dark,0,.055,-.02);          // top rail
  gbox(g,.062,.075,.26,0x5c616b,0,-.004,-.27);    // handguard
  gbox(g,.074,.012,.12,0xff7a1a,0,.036,-.05);     // orange accent
  gcyl(g,.014,.30,dark,0,.012,-.55);              // barrel
  gcyl(g,.024,.07,0x0f0f11,0,.012,-.70);          // muzzle brake
  gbox(g,.012,.045,.012,dark,0,.055,-.52);        // front sight
  gbox(g,.056,.10,.22,olive,0,-.015,.27);         // stock
  gbox(g,.062,.115,.03,0x111111,0,-.02,.39);      // butt pad
  gbox(g,.046,.12,.05,dark,0,-.105,.075,.28);     // pistol grip
  gbox(g,.04,.16,.07,0x3b3f2e,0,-.125,-.075,-.2); // magazine
  gbox(g,.05,.03,.06,0x2a2a2e,0,.083,-.03);       // red-dot body
  gbox(g,.018,.016,.006,new THREE.MeshBasicMaterial({color:0xff2222}),0,.086,-.062); // red-dot lens
  // hands + sleeves
  gbox(g,.062,.075,.095,skin,.0,-.145,.07);                         // right hand
  glimb(g,[.03,-.30,.40],[.0,-.15,.08],.085,sleeve);               // right arm
  gbox(g,.07,.06,.11,skin,0,-.065,-.27);                           // left hand
  glimb(g,[-.20,-.34,.22],[-.01,-.07,-.25],.085,sleeve);           // left arm
  const mf=makeMuzzleFlash(.26); mf.position.set(0,.012,-.78);
  g.add(mf); muzzleFlashes.push(mf);
  g.position.set(.22,-.21,-.36); g.scale.setScalar(.8);
  camera.add(g); gunGroups.push(g);
}

function buildSniper(){
  const g=new THREE.Group();
  const body=0x3a4733, dark=0x1c2216, wood=0x6a4a2e, skin=0xd9a98a, sleeve=0x2f4f3f;
  gbox(g,.06,.085,.36,body,0,0,0);                // receiver
  gcyl(g,.017,.55,dark,0,.01,-.52);               // barrel
  gcyl(g,.032,.24,0x0c0c0c,0,.01,-.90);           // suppressor
  gbox(g,.056,.07,.26,0x3a4630,0,-.005,-.30);     // forend
  gbox(g,.06,.12,.30,wood,0,-.02,.31);            // stock
  gbox(g,.05,.04,.16,0x222222,0,.05,.30);         // cheek rest
  gbox(g,.046,.12,.05,dark,0,-.105,.09,.28);      // grip
  gbox(g,.04,.09,.06,0x222a1c,0,-.085,-.04);      // magazine
  // scope
  gcyl(g,.03,.30,0x101010,0,.105,-.05);           // tube
  gcyl(g,.042,.08,0x101010,0,.105,-.21);          // front bell
  gcyl(g,.036,.06,0x101010,0,.105,.13);           // ocular
  gcyl(g,.035,.004,new THREE.MeshBasicMaterial({color:0x66ccff}),0,.105,-.252); // lens
  gbox(g,.02,.04,.03,0x222222,0,.065,-.13);       // mounts
  gbox(g,.02,.04,.03,0x222222,0,.065,.02);
  // bolt handle + folded bipod
  gbox(g,.012,.012,.05,0xaaaaaa,.05,.025,.10);
  gbox(g,.022,.022,.022,0xaaaaaa,.075,.025,.12);
  gbox(g,.008,.008,.20,0x333333,-.032,-.055,-.60);
  gbox(g,.008,.008,.20,0x333333,.032,-.055,-.60);
  // hands + sleeves
  gbox(g,.062,.075,.095,skin,0,-.15,.09);
  glimb(g,[.03,-.30,.42],[.0,-.15,.10],.085,sleeve);
  gbox(g,.07,.06,.11,skin,0,-.06,-.30);
  glimb(g,[-.20,-.34,.22],[-.01,-.065,-.30],.085,sleeve);
  const mf=makeMuzzleFlash(.30); mf.position.set(0,.01,-1.05);
  g.add(mf); muzzleFlashes.push(mf);
  g.position.set(.22,-.21,-.36); g.scale.setScalar(.8);
  g.visible=false;
  camera.add(g); gunGroups.push(g);
}

function animateGun(dt){
  const g=gunGroups[weaponIdx]; if(!g||!g.visible) return;
  gunKick=Math.max(0,gunKick-dt*8);
  gunBlend+=((gunMoving?1:0)-gunBlend)*Math.min(dt*10,1);
  if(gunMoving) gunBobT+=dt*(gunSprint?13:9);
  const amp=(gunSprint?.016:.008)*gunBlend, k=gunKick;
  const sprintK=gunSprint?gunBlend:0;
  g.position.x=.22+Math.cos(gunBobT*.5)*amp*.7;
  g.position.y=-.21+Math.abs(Math.sin(gunBobT))*amp-.02*sprintK-k*.012;
  g.position.z=-.36+k*.07;
  g.rotation.x=-k*.12+.10*sprintK;
  g.rotation.y=.16*sprintK;
  g.rotation.z=Math.sin(gunBobT*.5)*amp*1.5;
}

/* ─── REMOTE GUN MODELS ──────────────────────────────────────── */
function buildRemoteGun(idx){
  const g=new THREE.Group();
  const dm=mat(0x1e1e1e);
  if(idx===0){
    // Rifle — compact
    g.add(
      mobj(new THREE.BoxGeometry(.065,.065,.38),dm,0,0,-.12),
      mobj(new THREE.BoxGeometry(.09,.09,.18),mat(0x2a2a2a),0,-.02,.05),
    );
  } else {
    // Sniper — long barrel
    g.add(
      mobj(new THREE.BoxGeometry(.05,.05,.68),dm,0,0,-.22),
      mobj(new THREE.BoxGeometry(.085,.09,.20),mat(0x1a2810),0,-.015,.06),
      mobj(new THREE.BoxGeometry(.04,.04,.18),mat(0x0a0a0a),0,.055,-.04),  // scope
    );
  }
  // Position at right shoulder of the remote body
  g.position.set(.36,.08,-.14);
  return g;
}

/* ─── REMOTE PLAYER ──────────────────────────────────────────── */
function makeRemotePlayer(colorHex,name){
  const group=new THREE.Group();
  const c=new THREE.Color(colorHex);
  const cDark=new THREE.Color(colorHex).multiplyScalar(.55);
  const bm=new THREE.MeshLambertMaterial({color:c,flatShading:true});
  const dm=new THREE.MeshLambertMaterial({color:cDark,flatShading:true});

  const head =mobj(new THREE.BoxGeometry(.44,.44,.44),bm,0, .72,0);
  const torso=mobj(new THREE.BoxGeometry(.54,.62,.32),bm,0, .10,0);
  const armL =mobj(new THREE.BoxGeometry(.16,.54,.18),bm,-.38,.10,0);
  const armR =mobj(new THREE.BoxGeometry(.16,.54,.18),bm, .38,.10,0);
  const legL =mobj(new THREE.BoxGeometry(.19,.50,.19),dm,-.15,-.50,0);
  const legR =mobj(new THREE.BoxGeometry(.19,.50,.19),dm, .15,-.50,0);
  group.add(head,torso,armL,armR,legL,legR);

  // Name label
  const spr=makeLabel(name,colorHex);
  spr.position.y=1.5; group.add(spr);

  // Remote guns (both, toggle visible)
  const guns=[buildRemoteGun(0),buildRemoteGun(1)];
  guns[0].visible=true; guns[1].visible=false;
  guns.forEach(g=>group.add(g));

  group.userData.hittable=[head,torso,armL,armR,legL,legR];
  group.userData.headMesh=head;
  group.userData.legL=legL; group.userData.legR=legR;
  group.userData.armL=armL; group.userData.armR=armR;
  group.userData.bobT=0;
  group.userData.targetPos=new THREE.Vector3();
  group.userData.targetRot=0;
  group.userData.prevX=0; group.userData.prevZ=0;
  group.userData.remoteGuns=guns;
  return group;
}

function makeLabel(name,colorHex){
  const cvs=document.createElement('canvas');
  cvs.width=256; cvs.height=52;
  const ctx=cvs.getContext('2d');
  ctx.fillStyle='rgba(0,0,0,.6)'; ctx.fillRect(2,2,252,48);
  ctx.fillStyle=colorHex;
  ctx.font='bold 24px monospace';
  ctx.textAlign='center'; ctx.textBaseline='middle';
  ctx.fillText(name.substring(0,14),128,26);
  const tex=new THREE.CanvasTexture(cvs);
  const spr=new THREE.Sprite(new THREE.SpriteMaterial({map:tex,depthTest:false}));
  spr.scale.set(2,.42,1);
  return spr;
}

function setRemoteWeapon(id,idx){
  const op=otherPlayers[id]; if(!op) return;
  const guns=op.group.userData.remoteGuns;
  if(guns) guns.forEach((g,i)=>g.visible=i===idx);
}

function addRemote(p){
  if(otherPlayers[p.id]) return;
  const group=makeRemotePlayer(p.color,p.name);
  const bodyY=BODY_Y;
  group.position.set(p.x,bodyY,p.z);
  group.userData.targetPos.set(p.x,bodyY,p.z);
  group.userData.prevX=p.x; group.userData.prevZ=p.z;
  // Set initial weapon
  if(typeof p.weaponIdx==='number') setRemoteWeapon(p.id, p.weaponIdx);
  scene.add(group);
  otherPlayers[p.id]={group};
}

/* ─── INPUT ──────────────────────────────────────────────────── */
function initInput(){
  addEventListener('keydown',e=>{
    keys[e.code]=true;
    if(e.code==='Tab'){ e.preventDefault(); showSB(true); }
    if(e.code==='Escape') document.exitPointerLock();
    if(e.code==='Digit1') setWeapon(0);
    if(e.code==='Digit2') setWeapon(1);
    if(e.code==='Space'){ e.preventDefault(); jumpPressed=true; }
    if(e.code==='BracketLeft'||e.code==='Minus')  changeSens(-1);
    if(e.code==='BracketRight'||e.code==='Equal') changeSens(+1);
  });
  addEventListener('keyup',e=>{
    keys[e.code]=false;
    if(e.code==='Tab') showSB(false);
    if(e.code==='Space') jumpPressed=false;
  });
  addEventListener('mousemove',e=>{
    if(!pointerLocked) return;
    const mx=e.movementX, my=e.movementY;
    if(Math.abs(mx)>900||Math.abs(my)>900) return;   // ignore browser/OS glitch spikes
    yaw  -= mx*sensitivity;
    pitch = clamp(pitch-my*sensitivity,-PITCH_MAX,PITCH_MAX);
  });
  addEventListener('mousedown',e=>{ if(e.button===0) mouse.left=true; if(e.button===2) mouse.right=true; });
  addEventListener('mouseup',  e=>{ if(e.button===0) mouse.left=false; if(e.button===2) mouse.right=false; });
  addEventListener('contextmenu',e=>e.preventDefault());
  addEventListener('wheel',e=>{
    if(!gameStarted) return;
    setWeapon((weaponIdx+(e.deltaY>0?1:-1)+WEAPONS.length)%WEAPONS.length);
  });

  const cnv=document.getElementById('game-canvas');
  cnv.addEventListener('click',()=>lockPointer());
  document.addEventListener('pointerlockchange',()=>{
    pointerLocked=document.pointerLockElement===cnv;
    const lm=document.getElementById('lock-msg');
    lm.textContent=(game.t>0.5)?'[ PAUSED — CLICK TO RESUME ]':'[ CLICK TO ENTER COMBAT MODE ]';
    lm.style.display=(pointerLocked||game.over)?'none':'block';
  });
}

let sensToastT;
function changeSens(d){
  sensLevel=clamp(sensLevel+d,1,30);
  try{ localStorage.setItem('polySens',String(sensLevel)); }catch(e){}
  setTxt('sens-toast','SENSITIVITY  '+sensLevel+' / 30');
  setDisp('sens-toast','block');
  clearTimeout(sensToastT);
  sensToastT=setTimeout(()=>setDisp('sens-toast','none'),1100);
}

function setWeapon(idx){
  weaponIdx=idx;
  gunGroups.forEach((g,i)=>g.visible=i===idx);
  document.getElementById('weap-name').textContent=WEAPONS[idx].name;
  document.querySelectorAll('.wslot').forEach((el,i)=>el.classList.toggle('active',i===idx));
  playWeaponSwitch();
}

/* ─── GAME LOOP ──────────────────────────────────────────────── */
function gameLoop(now){
  requestAnimationFrame(gameLoop);
  const dt=Math.min((now-lastTime)/1000,.05);
  lastTime=now;
  if(gameStarted) update(dt,now);
  if(skyRig) skyRig.position.copy(camera.position);   // sky always centred on the player
  renderer.render(scene,camera);

  // small FPS counter (top-left)
  fpsFrames++;
  if(now-fpsLast>=500){ setTxt('fps-ind',Math.round(fpsFrames*1000/(now-fpsLast))+' FPS'); fpsFrames=0; fpsLast=now; }
}
let fpsFrames=0, fpsLast=0;

/* ─── UPDATE ─────────────────────────────────────────────────── */
const _dir  =new THREE.Vector3();
const _euler=new THREE.Euler(0,0,0,'YXZ');

function update(dt,now){
  camera.rotation.set(pitch,yaw,0,'YXZ');

  /* Scope */
  const wantScope=mouse.right&&alive;
  targetFOV   = wantScope?WEAPONS[weaponIdx].scopeFOV:NORMAL_FOV;
  currentFOV += (targetFOV-currentFOV)*Math.min(dt*13,1);
  if(Math.abs(camera.fov-currentFOV)>0.005){ camera.fov=currentFOV; camera.updateProjectionMatrix(); }
  // sensitivity follows the zoom: same on-screen feel at any FOV (sniper scope no longer insanely twitchy)
  sensitivity = sensLevel*SENS_PER_LEVEL*Math.tan(currentFOV*Math.PI/360)/TAN_NORMAL;

  const showScope=wantScope&&weaponIdx===1&&!game.over;
  if(!game.over) setDisp('crosshair',showScope?'none':'block');
  setDisp('scope-ov',showScope?'block':'none');
  if(gunGroups[weaponIdx]) gunGroups[weaponIdx].visible=!showScope;

  /* Dragon animation */
  updateDragon(dt);

  /* Local simulation: bot, fireballs, regen, timer (paused when mouse is unlocked) */
  if(pointerLocked&&!game.over) localSim(dt);

  /* Remote players */
  updateRemotes(dt);

  if(cloudGroup) cloudGroup.rotation.y+=dt*.004;
  animateGun(dt);
  if(!alive||!pointerLocked||!myId||game.over){ gunMoving=false; gunSprint=false; return; }

  /* ── Jump ── */
  if(jumpPressed&&onGround){
    velocityY=JUMP_FORCE;
    onGround=false;
    jumpPressed=false;
    playJump();
  }
  if(!onGround){
    velocityY-=GRAVITY*dt;
    camera.position.y+=velocityY*dt;
    if(camera.position.y<=PLAYER_HEIGHT){
      camera.position.y=PLAYER_HEIGHT;
      velocityY=0;
      onGround=true;
    }
  }

  /* ── Movement ── */
  _dir.set(0,0,0);
  if(keys['KeyW']||keys['ArrowUp'])    _dir.z-=1;
  if(keys['KeyS']||keys['ArrowDown'])  _dir.z+=1;
  if(keys['KeyA']||keys['ArrowLeft'])  _dir.x-=1;
  if(keys['KeyD']||keys['ArrowRight']) _dir.x+=1;

  const sprinting=(keys['ShiftLeft']||keys['ShiftRight'])&&_dir.lengthSq()>0;
  const speed=MOVE_SPEED*(sprinting?SPRINT_MULT:1);
  const moving=_dir.lengthSq()>0;
  gunMoving=moving; gunSprint=sprinting;
  setDisp('sprint-ind',sprinting?'block':'none');

  if(moving){
    _dir.normalize();
    _euler.set(0,yaw,0);
    _dir.applyEuler(_euler);
    const nx=camera.position.x+_dir.x*speed*dt;
    const nz=camera.position.z+_dir.z*speed*dt;
    const r=resolveCol(camera.position.x,camera.position.z,nx,nz);
    camera.position.x=r.x; camera.position.z=r.z;

    // Footsteps
    footstepTimer-=dt;
    if(footstepTimer<=0){ playFootstep(); footstepTimer=sprinting?.22:.38; }
  }

  /* ── Shoot ── */
  const w=WEAPONS[weaponIdx];
  if(mouse.left&&(w.auto||!mouse._wasLeft)&&now-lastShot>w.fireRate){
    lastShot=now; doShoot();
  }
  mouse._wasLeft=mouse.left;

}

/* ─── REMOTE INTERPOLATION + ANIMATION ──────────────────────── */
function updateRemotes(dt){
  const lf=1-Math.exp(-12*dt);
  for(const {group} of Object.values(otherPlayers)){
    const ud=group.userData;
    group.position.x+=(ud.targetPos.x-group.position.x)*lf;
    group.position.z+=(ud.targetPos.z-group.position.z)*lf;
    group.position.y+=(ud.targetPos.y-group.position.y)*lf;

    let dRot=ud.targetRot-group.rotation.y;
    while(dRot> Math.PI) dRot-=Math.PI*2;
    while(dRot<-Math.PI) dRot+=Math.PI*2;
    group.rotation.y+=dRot*lf;

    const dx=group.position.x-ud.prevX;
    const dz=group.position.z-ud.prevZ;
    ud.prevX=group.position.x; ud.prevZ=group.position.z;
    const isMoving=Math.sqrt(dx*dx+dz*dz)>0.005;

    if(isMoving){
      ud.bobT=(ud.bobT||0)+dt*9;
      const s=Math.sin(ud.bobT);
      if(ud.legL) ud.legL.rotation.x= s*.75;
      if(ud.legR) ud.legR.rotation.x=-s*.75;
      if(ud.armL) ud.armL.rotation.x=-s*.45;
      if(ud.armR) ud.armR.rotation.x= s*.45;
    } else {
      const decay=1-Math.exp(-8*dt);
      if(ud.legL) ud.legL.rotation.x*=(1-decay);
      if(ud.legR) ud.legR.rotation.x*=(1-decay);
      if(ud.armL) ud.armL.rotation.x*=(1-decay);
      if(ud.armR) ud.armR.rotation.x*=(1-decay);
    }
  }
}

/* ─── COLLISION ──────────────────────────────────────────────── */
function resolveCol(ox,oz,nx,nz){
  let rx=nx,rz=nz;
  for(const c of colliders){
    if(rx>c.minX&&rx<c.maxX&&rz>c.minZ&&rz<c.maxZ){
      const wasX=ox>c.minX&&ox<c.maxX;
      const wasZ=oz>c.minZ&&oz<c.maxZ;
      if(!wasX) rx=ox;
      else if(!wasZ) rz=oz;
      else { rx=ox; rz=oz; }
    }
  }
  return {x:rx,z:rz};
}

/* ─── SHOOT ──────────────────────────────────────────────────── */
const _ray =new THREE.Raycaster();
const _aim0=new THREE.Vector2(0,0);

function doShoot(){
  const w=WEAPONS[weaponIdx];
  // AIM FIX: matrices are normally refreshed only inside renderer.render(), i.e. AFTER update().
  // The ray therefore used last frame's camera/target positions -> shots landed behind your crosshair
  // (worse the faster you turn / the faster the dragon moves). Refresh them right before raycasting.
  camera.rotation.set(pitch,yaw,0,'YXZ');
  camera.updateMatrixWorld(true);
  if(dragonGroup) dragonGroup.updateMatrixWorld(true);
  for(const o of Object.values(otherPlayers)) o.group.updateMatrixWorld(true);
  if(weaponIdx===0) playRifleShot(); else playSniperShot();

  // Recoil (smooth spring in animateGun + small camera kick)
  const gun=gunGroups[weaponIdx];
  gunKick=Math.min(1,gunKick+(weaponIdx===0?.5:1));
  pitch=clamp(pitch+(weaponIdx===0?.0022:.016),-PITCH_MAX,PITCH_MAX);
  // Muzzle flash
  const mf=muzzleFlashes[weaponIdx];
  if(mf&&gun&&gun.visible){
    mf.material.opacity=1;
    clearTimeout(muzzleTimer);
    muzzleTimer=setTimeout(()=>{ if(mf) mf.material.opacity=0; },55);
  }

  const sp=w.spread;
  const aim=new THREE.Vector2(
    _aim0.x+(Math.random()-.5)*sp*2,
    _aim0.y+(Math.random()-.5)*sp*2,
  );
  _ray.setFromCamera(aim,camera);
  _ray.far=130;

  // ── Check dragon first ─────────────────────────────────────
  if(dragonHitMeshes.length>0){
    const dHits=_ray.intersectObjects(dragonHitMeshes);
    if(dHits.length>0){
      // Wall check for dragon too
      const wHits=_ray.intersectObjects(wallMeshes);
      const wDist=wHits.length>0?wHits[0].distance:Infinity;
      if(wDist>=dHits[0].distance){
        damageDragon(w.damage);
        flashHitMarker();
        return;   // bullet consumed by dragon
      }
    }
  }

  // ── Check players ──────────────────────────────────────────
  const meshToId=new Map();
  for(const [id,{group}] of Object.entries(otherPlayers)){
    if(!group.visible) continue;
    for(const m of (group.userData.hittable||[])) meshToId.set(m,id);
  }
  if(meshToId.size===0) return;

  const pHits=_ray.intersectObjects([...meshToId.keys()]);
  if(pHits.length===0) return;

  const pDist=pHits[0].distance;
  const wHits=_ray.intersectObjects(wallMeshes);
  const wDist=wHits.length>0?wHits[0].distance:Infinity;
  if(wDist<pDist) return;   // wall blocks shot

  const targetId=meshToId.get(pHits[0].object);
  if(!targetId) return;

  // ── Headshot detection ─────────────────────────────────────
  const targetOp=otherPlayers[targetId];
  let damage=w.damage;
  let isHeadshot=false;
  if(targetOp && pHits[0].object===targetOp.group.userData.headMesh){
    damage=w.headDmg;
    if(damage>w.damage) isHeadshot=true;
  }

  damageBot(damage,isHeadshot);
  flashHitMarker(isHeadshot);
  if(isHeadshot) showHeadshotIndicator();
}

/* ─── DRAGON CLIENT ──────────────────────────────────────────── */
function buildDragon(){
  dragonHitMeshes.length=0;
  const g=new THREE.Group();
  // fog:false + a little emissive glow -> the dragon stays visible against the dark red night sky at any distance
  const dmat=(c,e)=>new THREE.MeshLambertMaterial({color:c,emissive:e,flatShading:true,fog:false});
  const bm=dmat(0x2f7a40,0x3a0d05),dm=dmat(0x1c5228,0x2a0a04),wm=dmat(0x2a7a3e,0x3a0d05);

  function addHit(mesh){ dragonHitMeshes.push(mesh); return mesh; }

  g.add(addHit(mobj(new THREE.BoxGeometry(2.2,1.0,6.5),bm,0,0,0)));       // body
  const neck=mobj(new THREE.BoxGeometry(.9,.8,1.8),bm,0,.3,-3.5);
  neck.rotation.x=-.28; g.add(addHit(neck));
  g.add(addHit(mobj(new THREE.BoxGeometry(1.1,.9,1.8),bm,0,.5,-4.8)));    // head
  g.add(mobj(new THREE.BoxGeometry(.7,.45,.9),dm,0,.1,-5.6));             // snout

  [-0.35,0.35].forEach(x=>{
    const h=new THREE.Mesh(new THREE.ConeGeometry(.1,.7,4),dm);
    h.position.set(x,1.1,-4.7); h.rotation.z=x>.0?.3:-.3; g.add(h);
  });
  [-0.28,0.28].forEach(x=>{
    const e=new THREE.Mesh(new THREE.BoxGeometry(.12,.1,.06),
      new THREE.MeshBasicMaterial({color:0xffaa22,fog:false}));
    e.position.set(x,.6,-5.5); e.scale.setScalar(1.6); g.add(e);
  });
  for(let i=0;i<5;i++){
    const s=1-i*.17;
    g.add(mobj(new THREE.BoxGeometry(s*1.2,s*.8,1.1),i<2?bm:dm,0,-i*.09,3.2+i*1.1));
  }

  function wing(side){
    const piv=new THREE.Group();
    piv.position.set(side*1.1,.2,.5);
    const ua=new THREE.Mesh(new THREE.BoxGeometry(3.8,.11,1.8),wm);
    ua.position.set(side*2.2,.4,0); ua.rotation.z=side*.28; piv.add(ua); dragonHitMeshes.push(ua);
    const lm=new THREE.Mesh(new THREE.BoxGeometry(3.0,.09,3.2),wm);
    lm.position.set(side*5.0,-.1,.8); lm.rotation.z=side*.12; piv.add(lm); dragonHitMeshes.push(lm);
    g.add(piv);
    return piv;
  }
  g.userData.wingL=wing(-1);
  g.userData.wingR=wing(1);
  return g;
}

function spawnDragonClient(data){
  if(dragonGroup){ scene.remove(dragonGroup); }
  dragonGroup=buildDragon();
  scene.add(dragonGroup);
  dragonData={
    startAngle:     data.startAngle,
    // clientStartTime: when the dragon was at startAngle, expressed in performance.now() units
    simT: data.elapsed||0,          // sim clock: only advances while the game is running (pause = dragon stops)
    health:          data.health,
    maxHealth:       data.maxHealth,
  };
  playDragonRoar();
  showDragonMsg('⚠  DRAGON  INCOMING  ⚠','#ff6600');
  updateDragonHPBar(data.health,data.maxHealth);
  document.getElementById('dragon-hp-wrap').style.display='block';
}

function despawnDragonClient(data){
  if(dragonGroup){ scene.remove(dragonGroup); dragonGroup=null; }
  dragonHitMeshes.length=0;
  dragonData=null;
  envT=0; applyEnv(0);
  document.getElementById('dragon-hp-wrap').style.display='none';
  if(data&&data.killed){
    showDragonMsg(`🐉 DRAGON SLAIN BY ${esc(data.killerName)}!`,'#ffcc00');
    addKillFeed(data.killerName,'🐉 DRAGON');
  } else {
    showDragonMsg('DRAGON HAS FLED','#555555');
  }
}

function updateDragon(dt){
  if(!dragonData||!dragonGroup) return;
  if(pointerLocked&&!game.over) dragonData.simT+=dt;
  const elapsed=dragonData.simT;
  const dragonT=dragonData.startAngle+elapsed*cfg.dragonOmega;

  const R=40;
  dragonGroup.position.set(
    Math.cos(dragonT)*R,
    20+Math.sin(dragonT*1.8)*3.5,
    Math.sin(dragonT)*R,
  );
  dragonGroup.rotation.y=dragonT+Math.PI/2;
  dragonGroup.rotation.z=-Math.sin(dragonT)*.18;

  const ft=dragonT*5;
  dragonGroup.userData.wingL.rotation.z= Math.sin(ft)*.55;
  dragonGroup.userData.wingR.rotation.z=-Math.sin(ft)*.55;

  // Environment blend (fade in first 3s, full for middle, fade out last 3s of 40s duration)
  if(envT<1){ envT=Math.min(1,elapsed/3); applyEnv(envT); }   // only the 3s fade needs per-frame env updates
}

function applyEnv(t){
  const fr=ENV_NORMAL.fogR+(ENV_DRAGON.fogR-ENV_NORMAL.fogR)*t;
  const fg=ENV_NORMAL.fogG+(ENV_DRAGON.fogG-ENV_NORMAL.fogG)*t;
  const fb=ENV_NORMAL.fogB+(ENV_DRAGON.fogB-ENV_NORMAL.fogB)*t;
  _envCol.setRGB(fr,fg,fb);
  scene.fog.color.copy(_envCol); renderer.setClearColor(_envCol);
  scene.fog.near=ENV_NORMAL.fogNear+(ENV_DRAGON.fogNear-ENV_NORMAL.fogNear)*t;
  scene.fog.far =ENV_NORMAL.fogFar +(ENV_DRAGON.fogFar -ENV_NORMAL.fogFar )*t;
  ambientLight.color.setRGB(
    ENV_NORMAL.ambR+(ENV_DRAGON.ambR-ENV_NORMAL.ambR)*t,
    ENV_NORMAL.ambG+(ENV_DRAGON.ambG-ENV_NORMAL.ambG)*t,
    ENV_NORMAL.ambB+(ENV_DRAGON.ambB-ENV_NORMAL.ambB)*t,
  );
  sunLight.color.setRGB(
    ENV_NORMAL.sunR+(ENV_DRAGON.sunR-ENV_NORMAL.sunR)*t,
    ENV_NORMAL.sunG+(ENV_DRAGON.sunG-ENV_NORMAL.sunG)*t,
    ENV_NORMAL.sunB+(ENV_DRAGON.sunB-ENV_NORMAL.sunB)*t,
  );
  sunLight.intensity=ENV_NORMAL.sunInt+(ENV_DRAGON.sunInt-ENV_NORMAL.sunInt)*t;
  if(skyMat) skyMat.color.setRGB(1+(SKY_NIGHT.r-1)*t,1+(SKY_NIGHT.g-1)*t,1+(SKY_NIGHT.b-1)*t);
  // clouds were staying bright white at night (they are unlit/fog-free) -> tint them dark red too
  for(const m of cloudMats) m.color.setRGB(1-.7*t,1-.94*t,1-.95*t);
  if(sunMesh) sunMesh.visible=t<.5;
}

function updateDragonHPBar(hp,maxHp){
  const pct=Math.max(0,hp/maxHp)*100;
  const bar=document.getElementById('dragon-hp-bar');
  const txt=document.getElementById('dragon-hp-text');
  if(bar) bar.style.width=pct+'%';
  if(txt) txt.textContent=Math.max(0,hp)+' / '+maxHp;
}

let dragonFlashT;
function flashDragonHit(){
  const bar=document.getElementById('dragon-hp-bar');
  if(!bar) return;
  bar.style.background='#ffffff';
  clearTimeout(dragonFlashT);
  dragonFlashT=setTimeout(()=>bar.style.background='',80);
}

function showDragonMsg(msg,color){
  const el=document.getElementById('dragon-banner');
  const el2=document.getElementById('dragon-msg');
  el2.textContent=msg; el2.style.color=color||'#ff6600';
  el.style.display='block';
  setTimeout(()=>el.style.display='none',5000);
}

/* ─── UI ─────────────────────────────────────────────────────── */
let _hpShown=-1;
function updateHPUI(){
  const hp=clamp(myHealth,0,100);
  const hr=Math.round(hp); if(hr===_hpShown) return; _hpShown=hr;
  const bar=document.getElementById('hp-bar');
  bar.style.width=hp+'%';
  const cls=hp>60?'':hp>30?'mid':'low';
  bar.className=cls; document.getElementById('hud').className=cls;
  document.getElementById('hp-text').textContent=Math.round(hp);
}

let hitFlashT;
function showHitFlash(){
  const el=document.getElementById('hit-flash');
  el.style.display='block';
  clearTimeout(hitFlashT);
  hitFlashT=setTimeout(()=>el.style.display='none',115);
}

let hitMarkT;
function flashHitMarker(headshot=false){
  const ch=document.getElementById('crosshair');
  ch.classList.add('hit');
  ch.style.transform='translate(-50%,-50%) scale(1.7)';
  if(headshot) ch.style.filter='hue-rotate(200deg)';
  clearTimeout(hitMarkT);
  hitMarkT=setTimeout(()=>{
    ch.classList.remove('hit');
    ch.style.transform='translate(-50%,-50%) scale(1)';
    ch.style.filter='';
  },165);
}

let hsTimer;
function showHeadshotIndicator(){
  const el=document.getElementById('headshot-ind');
  el.style.display='block'; el.style.opacity='1';
  clearTimeout(hsTimer);
  hsTimer=setTimeout(()=>{
    el.style.opacity='0';
    setTimeout(()=>el.style.display='none',400);
  },900);
}

function addKillFeed(killer,victim){
  const kf=document.getElementById('killfeed');
  const d=document.createElement('div');
  d.className='ke';
  d.innerHTML=`<span style="color:#ff6622;font-weight:bold">${esc(killer)}</span>`
             +` ✕ <span style="color:#44ddff">${esc(victim)}</span>`;
  kf.prepend(d);
  while(kf.children.length>6) kf.removeChild(kf.lastChild);
  setTimeout(()=>d.remove(),3700);
}

function showSB(v){ document.getElementById('scoreboard').style.display=v?'block':'none'; }

function renderScoreboard(scores){
  const tb=document.getElementById('score-rows');
  tb.innerHTML='';
  [...scores].sort((a,b)=>b.kills-a.kills).forEach(p=>{
    const isMe=p.id===myId;
    const tr=document.createElement('tr');
    if(isMe) tr.style.background='rgba(0,255,65,.05)';
    tr.innerHTML=
      `<td><span style="color:${p.color}">${esc(p.name)}</span>`
      +(isMe?' <span style="color:#003311;font-size:10px">(you)</span>':'')+`</td>`
      +`<td style="color:#44ff88">${p.kills}</td>`
      +`<td style="color:#ff4444">${p.deaths}</td>`
      +`<td>${p.alive?`<span style="color:#00ff41">${p.health}</span>`:`<span style="color:#444">☠</span>`}</td>`;
    tb.appendChild(tr);
  });
}

function uiCount(n){
  document.getElementById('player-count').textContent=`◉ ${n} online`;
}

/* ═══════════════════════════════════════════════════════════════
   SINGLE PLAYER  —  PHASE 1: BOT DUEL  →  PHASE 2: DRAGON
   Target match length: ~3-4 minutes
   ═══════════════════════════════════════════════════════════════ */
const DRAGON_TIME_LIMIT = 150;   // seconds — dragon escapes if not killed in time

const DIFFS = {
  // bot HP is a multiple of the rifle damage (20): easy 5 hits, medium 6 hits, hard 7 hits
  easy:   { label:'EASY',   botHp:100, speed:4.8, fireMs:760, react:.80, acc:.22, dmg:7,
            dragonHp:600,  fbEvery:3.8, fbSpeed:15, fbDmg:16, dragonOmega:.27 },
  medium: { label:'MEDIUM', botHp:120, speed:6.2, fireMs:460, react:.50, acc:.40, dmg:9,
            dragonHp:1000, fbEvery:2.9, fbSpeed:19, fbDmg:21, dragonOmega:.34 },
  hard:   { label:'HARD',   botHp:140, speed:8.0, fireMs:280, react:.30, acc:.60, dmg:11,
            dragonHp:1500, fbEvery:2.1, fbSpeed:23, fbDmg:26, dragonOmega:.42 },
};
let cfg = DIFFS.medium;
function setDifficulty(k){ cfg = DIFFS[k] || DIFFS.medium; }

const game = {
  phase:'idle',        // idle | duel | transition | dragon | over
  t:0, phaseT:0, over:false,
  kills:0, deaths:0, headshots:0,
  lastDmgT:-99, lastDmgBy:'',
};
const bot = { alive:false, x:0, z:0, hp:0, max:0, strafe:1, strafeT:0,
              lastShot:0, seeT:0, stuck:0, evade:0, evx:0, evz:0, vx:0, vz:0, flipCd:0, group:null };

const fireballs = [];
const fxList    = [];
let dragonFbT = 3, dragonPhaseT = 0;
let wallBoxes = null;
const _losRay = new THREE.Raycaster();

/* ─── extra sounds ───────────────────────────────────────────── */
function playBotShot(dist){ try{ const c=getAudio(); const v=Math.max(.08,.45-dist/120); _noiseBurst(c,700,.07,v,.4); _oscBurst(c,110,45,.08,v*.6); }catch(e){} }
function playHurt(){        try{ const c=getAudio(); _oscBurst(c,220,80,.14,.22,'square'); }catch(e){} }
function playFireball(){    try{ const c=getAudio(); _noiseBurst(c,240,.35,.45,.3); _oscBurst(c,120,45,.4,.2,'sawtooth'); }catch(e){} }
function playExplosion(){   try{ const c=getAudio(); _noiseBurst(c,170,.45,.75,.3); _oscBurst(c,70,25,.4,.3,'sawtooth'); }catch(e){} }
function playWin(){         try{ const c=getAudio(); [0,.15,.3,.5].forEach((d,i)=>setTimeout(()=>_oscBurst(c,440*Math.pow(1.26,i),440*Math.pow(1.26,i)*1.01,.25,.2,'triangle'),d*1000)); }catch(e){} }

/* ─── init ───────────────────────────────────────────────────── */
function initLocalGame(){
  myId='player'; alive=true; myHealth=100; updateHPUI();
  camera.position.set(-15,PLAYER_HEIGHT,-15);
  yaw=Math.atan2(-30,-30); pitch=0;

  const grp=makeRemotePlayer('#ff4455','BOT · '+cfg.label);
  grp.position.set(15,BODY_Y,15);
  grp.userData.targetPos.set(15,BODY_Y,15);
  grp.userData.prevX=15; grp.userData.prevZ=15;
  bot.bar=makeBotBar(); grp.add(bot.bar);
  scene.add(grp);
  otherPlayers.bot={group:grp};
  bot.group=grp; bot.x=15; bot.z=15; bot.hp=bot.max=cfg.botHp; bot.alive=true;
  bot.lastShot=1500;

  game.phase='duel'; drawBotBar();
  setBossBar('🤖 BOT · '+cfg.label, bot.hp, bot.max);
  document.getElementById('dragon-hp-wrap').style.display='block';
  document.getElementById('player-count').textContent='◉ VS BOT · '+cfg.label;
  document.getElementById('room-ind').textContent='◈ SINGLE PLAYER';
  document.getElementById('match-hud').style.display='block';
  refreshScoreboard();
  showDragonMsg('⚔  PHASE 1 : DEFEAT THE BOT  ⚔','#00ff88');
}

function makeBotBar(){
  const c=document.createElement('canvas'); c.width=128; c.height=16;
  const tex=new THREE.CanvasTexture(c);
  const spr=new THREE.Sprite(new THREE.SpriteMaterial({map:tex,depthTest:false,transparent:true}));
  spr.scale.set(1.6,.2,1); spr.position.y=1.85; spr.renderOrder=10;
  spr.userData={c,tex};
  return spr;
}
function drawBotBar(){
  const {c,tex}=bot.bar.userData; const x=c.getContext('2d');
  x.clearRect(0,0,128,16); x.fillStyle='rgba(0,0,0,.7)'; x.fillRect(0,0,128,16);
  const f=Math.max(0,bot.hp/bot.max);
  x.fillStyle=f>.5?'#35ff6a':f>.25?'#ffcc22':'#ff3322'; x.fillRect(2,2,124*f,12);
  tex.needsUpdate=true;
}
let _arrDeg=999;
function updateBotIndicator(){
  // red arrow + distance: points at the BOT in phase 1 and at the DRAGON in phase 2
  let tx,tz,ty=0,label;
  if(game.phase==='duel'&&bot.alive){ tx=bot.x; tz=bot.z; ty=1.2; label='BOT'; }
  else if(game.phase==='dragon'&&dragonGroup&&game.over===false){ const p=dragonGroup.position; tx=p.x; tz=p.z; ty=p.y; label='DRAGON'; }
  else { setDisp('bot-ind','none'); return; }
  const dx=tx-camera.position.x, dz=tz-camera.position.z;
  const fx=-Math.sin(yaw), fz=-Math.cos(yaw), rx=Math.cos(yaw), rz=-Math.sin(yaw);
  const ang=Math.atan2(dx*rx+dz*rz, dx*fx+dz*fz);
  const hd=Math.hypot(dx,dz);
  bot.dist=hd;
  setDisp('bot-ind','block');
  const deg=Math.round(ang*180/Math.PI);
  if(deg!==_arrDeg){
    _arrDeg=deg;
    const ar=$('bot-arrow');
    ar.style.transform='rotate('+deg+'deg)';
    ar.style.opacity=Math.abs(ang)<.45?'0':'1';
  }
  // vertical hint when the target is above/below the screen
  const elev=Math.atan2(ty-camera.position.y,hd);
  const dv=elev-pitch;
  const vh=Math.abs(ang)<.9&&Math.abs(dv)>.5 ? (dv>0?'  ▲ LOOK UP':'  ▼ LOOK DOWN') : '';
  setTxt('bot-dist',label+' '+Math.round(Math.hypot(hd,ty-camera.position.y))+'m'+vh);
}

function setBossBar(label,hp,max){
  document.getElementById('dragon-hp-label').textContent=label;
  updateDragonHPBar(Math.max(0,Math.round(hp)),max);
}

/* ─── main sim ───────────────────────────────────────────────── */
function localSim(dt){
  game.t+=dt;

  // health regen after 4s without damage
  if(alive && myHealth<100 && game.t-game.lastDmgT>4){
    myHealth=Math.min(100,myHealth+5*dt); updateHPUI();
  }

  if(game.phase==='duel') updateBot(dt);
  else if(game.phase==='transition'){
    game.phaseT-=dt; bot.deadT=(bot.deadT||0)+dt;
    bot.group.rotation.x=-Math.min(bot.deadT*3.2,1.5);
    if(game.phaseT<=0){ bot.group.visible=false; startDragonPhase(); }
  }
  else if(game.phase==='dragon') updateDragonPhase(dt);

  updateFireballs(dt);
  updateFx(dt);
  updateMatchHud();
}

/* ─── BOT AI ─────────────────────────────────────────────────── */
function updateBot(dt){
  if(!bot.alive) return;
  const now=game.t*1000;
  const px=camera.position.x, pz=camera.position.z;
  const dx=px-bot.x, dz=pz-bot.z;
  const dist=Math.hypot(dx,dz)||0.001;
  const nx=dx/dist, nz=dz/dist;

  // ── movement: smooth steering. (Old version switched direction by hard distance zones every frame and
  //    flipped strafe EVERY frame while touching a wall -> the bot vibrated / jittered.)
  bot.strafeT-=dt; bot.flipCd-=dt;
  if(bot.strafeT<=0){ bot.strafe=Math.random()<.5?-1:1; bot.strafeT=1.2+Math.random()*1.8; }
  const toward=clamp((dist-13)/9,-1,1);              // continuous: hold ~13m, ease in/out
  let mx=nx*toward + (-nz)*bot.strafe*.85;
  let mz=nz*toward + ( nx)*bot.strafe*.85;
  if(bot.evade>0){ bot.evade-=dt; mx=bot.evx; mz=bot.evz; }
  const ml=Math.hypot(mx,mz)||1; mx/=ml; mz/=ml;

  const acc=1-Math.exp(-6*dt);                       // velocity easing (no instant direction snaps)
  bot.vx+=(mx*cfg.speed-bot.vx)*acc;
  bot.vz+=(mz*cfg.speed-bot.vz)*acc;

  const tx=clamp(bot.x+bot.vx*dt,-MAP_HALF+2,MAP_HALF-2);
  const tz=clamp(bot.z+bot.vz*dt,-MAP_HALF+2,MAP_HALF-2);
  const r=resolveCol(bot.x,bot.z,tx,tz);
  const want=Math.hypot(bot.vx,bot.vz)*dt;
  const moved=Math.hypot(r.x-bot.x,r.z-bot.z);
  if(want>0.002 && moved<want*.4){
    bot.stuck+=dt;
    if(bot.stuck>.45 && bot.flipCd<=0){ bot.strafe*=-1; bot.strafeT=1.2+Math.random(); bot.flipCd=1.0; }
    if(bot.stuck>1.1){                               // really stuck -> walk back toward the arena centre
      const a=Math.atan2(-bot.z,-bot.x)+(Math.random()-.5)*1.6;
      bot.evx=Math.cos(a); bot.evz=Math.sin(a); bot.evade=.9; bot.stuck=0;
    }
  } else bot.stuck=Math.max(0,bot.stuck-dt*2);
  bot.x=r.x; bot.z=r.z;

  const ud=bot.group.userData;
  ud.targetPos.set(bot.x,BODY_Y,bot.z);
  ud.targetRot=Math.atan2(-dx,-dz);

  // line of sight
  const eye=new THREE.Vector3(bot.x,1.5,bot.z);
  const tgt=camera.position.clone();
  const dir=tgt.clone().sub(eye); const d3=dir.length(); dir.normalize();
  _losRay.set(eye,dir); _losRay.far=d3;
  const wh=_losRay.intersectObjects(wallMeshes);
  const los=wh.length===0;

  if(los) bot.seeT+=dt; else bot.seeT=0;

  if(los && bot.seeT>cfg.react && dist<50 && now-bot.lastShot>cfg.fireMs && alive){
    bot.lastShot=now+Math.random()*cfg.fireMs*.35;
    playBotShot(dist);
    let p=cfg.acc*(1-Math.min(dist,55)/90);
    if(keys['ShiftLeft']||keys['ShiftRight']) p*=.75;
    if(!onGround) p*=.7;
    const hit=Math.random()<p;
    const end=tgt.clone();
    if(!hit){ end.x+=(Math.random()-.5)*3.2; end.y+=(Math.random()-.5)*2; end.z+=(Math.random()-.5)*3.2; }
    spawnTracer(eye,end,0xff6655);
    if(hit) damagePlayer(cfg.dmg,'BOT');
  }
}

function botKilled(){
  bot.alive=false; bot.deadT=0;
  bot.group.userData.hittable=[];
  bot.bar.visible=false;
  bot.group.userData.targetPos.set(bot.x,.35,bot.z);
  game.kills++;
  addKillFeed(myName,'BOT');
  spawnExplosion(new THREE.Vector3(bot.x,1.2,bot.z),2.2);
  playExplosion();
  game.phase='transition'; game.phaseT=3;
  document.getElementById('dragon-hp-wrap').style.display='none';
  showDragonMsg('☠ BOT DOWN — DRAGON INCOMING','#ffcc00');
  refreshScoreboard();
}

function damageBot(d,head){
  if(!bot.alive||game.phase!=='duel'||game.over) return;
  bot.hp-=d;
  if(head) game.headshots++;
  setBossBar('🤖 BOT · '+cfg.label, bot.hp, bot.max); drawBotBar();
  flashDragonHit(); playHitSound();
  if(bot.hp<=0) botKilled();
}

/* ─── PLAYER DAMAGE / DEATH ──────────────────────────────────── */
function damagePlayer(d,by){
  if(!alive||game.over) return;
  myHealth-=d; game.lastDmgT=game.t; game.lastDmgBy=by;
  showHitFlash(); playHurt(); updateHPUI();
  if(myHealth<=0){
    myHealth=0; updateHPUI(); alive=false; game.deaths++;
    refreshScoreboard();
    endGame(false, by==='DRAGON' ? 'BURNED BY THE DRAGON' : 'KILLED BY THE BOT');
  }
}

/* ─── DRAGON PHASE ───────────────────────────────────────────── */
function startDragonPhase(){
  game.phase='dragon'; dragonPhaseT=0; dragonFbT=3.5;
  spawnDragonClient({startAngle:Math.random()*Math.PI*2, elapsed:0,
                     health:cfg.dragonHp, maxHealth:cfg.dragonHp});
  setBossBar('🐉 DRAGON', cfg.dragonHp, cfg.dragonHp);
}

function updateDragonPhase(dt){
  dragonPhaseT+=dt;
  if(dragonPhaseT>DRAGON_TIME_LIMIT){ endGame(false,'THE DRAGON ESCAPED'); return; }
  if(!dragonGroup||!dragonData) return;
  dragonFbT-=dt;
  if(dragonFbT<=0){
    fireFireball();
    const enraged=dragonData.health<dragonData.maxHealth*.3;
    dragonFbT=cfg.fbEvery*(.75+Math.random()*.5)*(enraged?.6:1);
  }
}

function damageDragon(d){
  if(!dragonData||game.phase!=='dragon'||game.over) return;
  dragonData.health-=d;
  updateDragonHPBar(Math.max(0,dragonData.health),dragonData.maxHealth);
  flashDragonHit(); playHitSound();
  if(dragonData.health<=0){
    const pos=dragonGroup?dragonGroup.position.clone():null;
    despawnDragonClient({killed:true,killerName:myName});
    if(pos){ spawnExplosion(pos,7); playExplosion(); }
    game.kills++;
    endGame(true,'DRAGON SLAIN');
  }
}

/* ─── FIREBALLS ──────────────────────────────────────────────── */
function fireFireball(){
  const start=dragonGroup.localToWorld(new THREE.Vector3(0,.5,-5.2));
  const target=camera.position.clone();
  target.x+=(Math.random()-.5)*2; target.z+=(Math.random()-.5)*2;
  const dir=target.sub(start).normalize();
  // fog:false -> fireballs never fade into the red night fog (you could not see them coming from far away)
  const core=new THREE.Mesh(new THREE.SphereGeometry(.6,8,6),
    new THREE.MeshBasicMaterial({color:0xffb030,fog:false}));
  const glow=new THREE.Mesh(new THREE.SphereGeometry(1.4,8,6),
    new THREE.MeshBasicMaterial({color:0xff3300,transparent:true,opacity:.35,fog:false}));
  core.add(glow);
  core.position.copy(start); scene.add(core);
  fireballs.push({mesh:core, vel:dir.multiplyScalar(cfg.fbSpeed), life:0});
  playFireball();
}

function getWallBoxes(){
  if(!wallBoxes){
    scene.updateMatrixWorld(true);
    wallBoxes=wallMeshes.map(m=>new THREE.Box3().setFromObject(m));
  }
  return wallBoxes;
}

function updateFireballs(dt){
  for(let i=fireballs.length-1;i>=0;i--){
    const f=fireballs[i];
    f.life+=dt;
    f.mesh.position.addScaledVector(f.vel,dt);
    f.mesh.rotation.x+=dt*5; f.mesh.rotation.y+=dt*3;
    const p=f.mesh.position;

    let explode=false, direct=false;
    const pc=camera.position;
    if(alive && Math.hypot(p.x-pc.x,p.z-pc.z)<1.0 && Math.abs(p.y-(pc.y-.4))<1.5){ explode=true; direct=true; }
    else if(p.y<.3 || f.life>8 || Math.abs(p.x)>MAP_HALF+25 || Math.abs(p.z)>MAP_HALF+25) explode=true;
    else {
      for(const b of getWallBoxes()){ if(b.containsPoint(p)){ explode=true; break; } }
    }
    if(explode){
      spawnExplosion(p.clone(),3.2); playExplosion();
      if(direct) damagePlayer(cfg.fbDmg,'DRAGON');
      else if(alive){
        const dd=Math.hypot(p.x-pc.x,p.y-(pc.y-.4),p.z-pc.z);
        if(dd<3.8) damagePlayer(Math.round(cfg.fbDmg*.45),'DRAGON');
      }
      scene.remove(f.mesh);
      f.mesh.geometry.dispose(); f.mesh.material.dispose();
      f.mesh.children.forEach(c=>{ c.geometry.dispose(); c.material.dispose(); });
      fireballs.splice(i,1);
    }
  }
}

/* ─── EFFECTS ────────────────────────────────────────────────── */
function spawnTracer(a,b,color){
  const dir=b.clone().sub(a); const len=dir.length();
  const m=new THREE.Mesh(new THREE.BoxGeometry(.05,.05,len),
    new THREE.MeshBasicMaterial({color,transparent:true,opacity:.9}));
  m.position.copy(a).addScaledVector(dir,.5); m.lookAt(b);
  scene.add(m); fxList.push({mesh:m,t:0,dur:.12,type:'tracer',size:1});
}
function spawnExplosion(pos,size){
  const m=new THREE.Mesh(new THREE.SphereGeometry(1,10,8),
    new THREE.MeshBasicMaterial({color:0xff8a00,transparent:true,opacity:.85}));
  m.position.copy(pos); scene.add(m);
  fxList.push({mesh:m,t:0,dur:.5,type:'boom',size});
}
function updateFx(dt){
  for(let i=fxList.length-1;i>=0;i--){
    const f=fxList[i]; f.t+=dt;
    const k=Math.min(f.t/f.dur,1);
    if(f.type==='tracer'){ f.mesh.material.opacity=.9*(1-k); }
    else {
      const s=.4+f.size*k; f.mesh.scale.set(s,s,s);
      f.mesh.material.opacity=.85*(1-k);
      f.mesh.material.color.setHex(k<.4?0xffcc33:0xff4400);
    }
    if(k>=1){
      scene.remove(f.mesh); f.mesh.geometry.dispose(); f.mesh.material.dispose();
      fxList.splice(i,1);
    }
  }
}

/* ─── HUD / SCOREBOARD / END ─────────────────────────────────── */
function fmtTime(t){ t=Math.max(0,Math.floor(t)); return String(Math.floor(t/60)).padStart(2,'0')+':'+String(t%60).padStart(2,'0'); }

function updateMatchHud(){
  if(game.phase==='duel')            setTxt('match-phase','PHASE 1 · BOT DUEL');
  else if(game.phase==='transition') setTxt('match-phase','DRAGON INCOMING...');
  else if(game.phase==='dragon')     setTxt('match-phase','PHASE 2 · DRAGON  (escapes in '+fmtTime(DRAGON_TIME_LIMIT-dragonPhaseT)+')');
  setTxt('match-time',fmtTime(game.t));
  updateBotIndicator();
}

function refreshScoreboard(){
  renderScoreboard([
    {id:'player',name:myName,color:'#44ff88',kills:game.kills,deaths:game.deaths,alive:alive,health:Math.round(myHealth)},
    {id:'bot',name:'BOT · '+cfg.label,color:'#ff4455',kills:game.deaths,deaths:bot.alive?0:1,alive:bot.alive,health:Math.round(bot.hp)},
  ]);
}

function endGame(win,reason){
  if(game.over) return;
  game.over=true; game.phase='over';
  mouse.left=false; mouse.right=false;
  setDisp('crosshair','none'); setDisp('scope-ov','none'); setDisp('bot-ind','none');
  document.getElementById('lock-msg').style.display='none';
  try{ document.exitPointerLock(); }catch(e){}

  const r=document.getElementById('result-screen');
  const t=document.getElementById('result-title');
  t.textContent=win?'VICTORY':'DEFEAT';
  t.style.color=win?'#00ff88':'#ff2222';
  t.style.textShadow=win?'0 0 40px rgba(0,255,136,.6)':'0 0 40px rgba(255,0,0,.6)';
  document.getElementById('result-reason').textContent=reason;
  const rs=(k,v)=>`<div class="rs"><span>${k}</span><b>${v}</b></div>`;
  document.getElementById('result-stats').innerHTML=
    rs('LEVEL',cfg.label)+rs('TIME',fmtTime(game.t))+rs('HEADSHOTS',game.headshots)+
    rs('BOT',(game.kills>=1&&!bot.alive)?'KILLED':'ALIVE')+rs('DRAGON',win?'SLAIN':'ALIVE')+rs('KILLS',game.kills);
  r.style.display='flex';
  if(win) playWin();
}
