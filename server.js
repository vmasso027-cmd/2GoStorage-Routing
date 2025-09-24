require("dotenv").config();
const express = require("express");
const fetch = (...args) => import("node-fetch").then(({default: f}) => f(...args));

const app = express();
const PORT = process.env.PORT || 8787;
const AIRTABLE_PAT = process.env.AIRTABLE_PAT;       // <-- from Part A
const BASE_ID = process.env.AIRTABLE_BASE_ID;        // <-- from Part A
const JOBS_TABLE = process.env.JOBS_TABLE || "2GoStorage Jobs";
const TRUCKS_TABLE = process.env.TRUCKS_TABLE || "Trucks";
const DRIVERS_TABLE = process.env.DRIVERS_TABLE || "Drivers";

// Origins
const ORIGIN_DEFAULT = { lat: 18.185554269901573, lng: -65.97009540669629 };
const BAYAMON_WHSE   = { lat: 18.40473159317047,  lng: -66.178846296465 };

// Heuristics
const AVERAGE_SPEED_KMH = 38;
const MAX_WAYPOINTS = 25;

const norm = s => String(s||"").normalize("NFD").replace(/[\u0300-\u036f]/g,"").toLowerCase().trim();
const isCanceled = status => norm(status).startsWith("cancel");
const loadState = (servicio, fromText) => {
  const s=norm(servicio), f=norm(fromText||"");
  if (s.startsWith("entrega") || s.startsWith("delivery")) return "empty";
  if (s.startsWith("recogido") || s.includes("to whse") || s.includes("llevar a whse") || s.includes("to warehouse")) return "full";
  if (s.startsWith("relocalizacion") || s.startsWith("relocation")) {
    const fromWhse = /(whse|warehouse|almacen|almac[eé]n|bayamon)/.test(f);
    return fromWhse ? "empty" : "full";
  }
  return "unknown";
};
const isWhseOrigin = fromText => /(whse|warehouse|almacen|almac[eé]n|bayamon)/.test(norm(fromText||""));
const parseLatLngAny = s => { if(!s) return null; const m=String(s).match(/(-?\d+\.\d+)\s*,\s*(-?\d+\.\d+)/); return m?{lat:+m[1],lng:+m[2]}:null; };
const lenFtFromTipo = tipo => {
  if (!tipo) return null;
  const m = String(tipo).match(/(\d+)\s*x\s*(\d+)\s*x?\s*(\d+)?/i);
  if (m) { const nums = m.slice(1).filter(Boolean).map(Number); return Math.max(...nums); }
  const map = { "8x8":8,"8x12":12,"8x16":16,"pop-up":20,"modular standard":20,"modular custom":20,"event pod":8,"guard house":8,"cold storage":10 };
  const key = norm(tipo); for (const k in map) if (key.includes(k)) return map[k]; return null;
};
const deriveTruckProfile = t => {
  const typeS = norm(t.fields?.["Types of Trucks"]);
  const bed   = Number(t.fields?.["Largo de Plataforma (ft)"]||0) || 0;
  const id    = String(t.fields?.["Camion"] || t.fields?.["Name"] || t.id);
  let code="Unknown";
  if (typeS.includes("remolque") || typeS.includes("trailer") || bed>=40) code="Trailer";
  else if (/(fingger|finger|knuckle|grua)/.test(typeS)) code="Fingger";
  else if (/flat\s*bed/.test(typeS)) code="Flatbed";
  return { id, code, bedFt:bed, rec:t };
};
const canCarry = (profile, load, L=0) => {
  if (profile.code==="Fingger") { if (L>=20) return false; if ((L===12||L===16)&&load==="full") return false; return true; }
  if (profile.code==="Flatbed") return true;
  if (profile.code==="Trailer") return true;
  return true;
};

const R=6371e3, toRad=d=>d*Math.PI/180;
const haversineMeters = (a,b) => {
  const dφ=toRad(b.lat-a.lat), dλ=toRad(b.lng-a.lng);
  const φ1=toRad(a.lat), φ2=toRad(b.lat);
  const s=Math.sin(dφ/2)**2 + Math.cos(φ1)*Math.cos(φ2)*Math.sin(dλ/2)**2;
  return 2*R*Math.asin(Math.sqrt(s));
};
const nnOrder = (origin, pts) => {
  const remaining = pts.slice(); const out = [origin]; let cur = origin;
  while (remaining.length){
    let bi=0, bd=Infinity;
    for (let i=0;i<remaining.length;i++){
      const d = haversineMeters(cur, remaining[i].coord);
      if (d<bd){ bd=d; bi=i; }
    }
    const nxt = remaining.splice(bi,1)[0];
    out.push(nxt); cur = nxt.coord;
  }
  out.push(origin); return out;
};
const pathCost = p => { let s=0;
  for (let i=0;i<p.length-1;i++){
    const a = (p[i].lat!==undefined)? p[i] : p[i].coord;
    const b = (p[i+1].lat!==undefined)? p[i+1] : p[i+1].coord;
    s += haversineMeters(a,b);
  } return s;
};
const twoOpt = path => {
  let best = path.slice(), improved = true;
  while (improved){
    improved=false;
    for (let i=1;i<best.length-2;i++){
      for (let k=i+1;k<best.length-1;k++){
        const np = best.slice(0,i).concat(best.slice(i,k+1).reverse(), best.slice(k+1));
        if (pathCost(np)+50 < pathCost(best)){ best=np; improved=true; }
      }
    }
  } return best;
};
const mapsUrlsForOrderedPath = ordered => {
  const asCoord = o => (o.lat!==undefined) ? {lat:o.lat,lng:o.lng} : o.coord;
  const coords = ordered.map(asCoord);
  const seen = new Map();
  const jitter=(lat,lng,n)=>{ const dLat=1/110574, dLng=1/(111320*0.949);
    const dx=(n%2?1:-1)*6*dLng*(1+Math.floor(n/2))*0.4;
    const dy=(n%3?1:-1)*6*dLat*(1+Math.floor(n/3))*0.6;
    return { lat:+(lat+dy).toFixed(8), lng:+(lng+dx).toFixed(8) };
  };
  const coordsSafe = coords.map(c=>{
    const key=`${c.lat},${c.lng}`; const n=seen.get(key)||0; seen.set(key,n+1);
    return n?jitter(c.lat,c.lng,n):c;
  });
  const urls=[]; let startIdx=0;
  while (startIdx<coordsSafe.length-1){
    const endIdx=Math.min(startIdx+(MAX_WAYPOINTS-1), coordsSafe.length-1);
    const slice=coordsSafe.slice(startIdx,endIdx+1);
    const origin=slice[0], dest=slice[slice.length-1];
    const wps=slice.slice(1,-1).map(c=>`${c.lat},${c.lng}`).join("|");
    const u=`https://www.google.com/maps/dir/?api=1&origin=${encodeURIComponent(`${origin.lat},${origin.lng}`)}&destination=${encodeURIComponent(`${dest.lat},${dest.lng}`)}${wps?`&waypoints=${encodeURIComponent(wps)}`:""}&travelmode=driving`;
    urls.push(u); startIdx=endIdx;
  } return urls;
};

async function listAll(tableName){
  const out=[]; let offset=undefined;
  do{
    const url = new URL(`https://api.airtable.com/v0/${BASE_ID}/${encodeURIComponent(tableName)}`);
    url.searchParams.set("pageSize","100");
    if (offset) url.searchParams.set("offset", offset);
    const res=await fetch(url.toString(),{headers:{Authorization:`Bearer ${AIRTABLE_PAT}`}});
    if (!res.ok) throw new Error(`Airtable ${tableName} ${res.status}`);
    const json=await res.json(); out.push(...(json.records||[])); offset=json.offset;
  }while(offset);
  return out;
}

app.get("/suggest_routes", async (req, res) => {
  try{
    const onlyUnassigned = String(req.query.only_unassigned||"true")==="true";
    const maxJobsPerTruck = Number(req.query.max_jobs_per_truck||5);

    const [jobs, trucks, drivers] = await Promise.all([
      listAll(JOBS_TABLE), listAll(TRUCKS_TABLE), listAll(DRIVERS_TABLE)
    ]);

    // Candidates (exclude only Cancelado; optionally ignore already-assigned)
    const cand = jobs.map(r=>{
      const status = r.fields?.Status || "";
      if (isCanceled(status)) return null;
      const choferLinked = r.fields?.Chofer;
      if (onlyUnassigned && Array.isArray(choferLinked) && choferLinked.length) return null;
      const dest = r.fields?.["Destination Address"] || "";
      const cli  = r.fields?.["Destination address from client"] || "";
      const coord = parseLatLngAny(dest) || parseLatLngAny(cli);
      if (!coord) return null;
      const servicio = r.fields?.Servicio || "";
      const fromText = r.fields?.From || "";
      const tipo     = r.fields?.Tipo || "";
      const lenFt    = r.fields?.["Largo (ft)"] ?? lenFtFromTipo(tipo);
      const load     = loadState(servicio, fromText);
      return { id: r.fields?.Jobs || r.id, coord, servicio, fromText, tipo, lenFt, load, whseFrom: isWhseOrigin(fromText) };
    }).filter(Boolean);

    // Available trucks & drivers
    const units = trucks.filter(t=> norm(t.fields?.Status)==="available").map(deriveTruckProfile);
    const driverByTruck = new Map();
    for (const d of drivers){
      if (norm(d.fields?.Status)!=="available") continue;
      const tLink=d.fields?.Trucks;
      if (Array.isArray(tLink) && tLink.length>0) driverByTruck.set(tLink[0].name, d.fields?.Name || d.id);
    }
    if (!units.length) return res.json({ generated_at: new Date().toISOString(), origin: ORIGIN_DEFAULT, suggestions: [] });

    // Group by type, partition, order, summarize
    const types = Array.from(new Set(units.map(u=>u.code)));
    const suggestions=[];
    for (const type of types){
      const unitsOfType = units.filter(u=>u.code===type);
      const bedFt = unitsOfType[0]?.bedFt || 24;

      const feasible = cand.filter(j=> canCarry(unitsOfType[0], j.load, j.lenFt));

      function partition(origin, jobs, K, bed){
        if (!jobs.length || !K) return Array.from({length:K},()=>[]);
        const withAngle = jobs.map(j=>({...j, angle: Math.atan2(j.coord.lat-origin.lat, j.coord.lng-origin.lng)}))
                              .sort((a,b)=> a.angle - b.angle);
        const bins = Array.from({length:K}, ()=>({loadFt:0, arr:[]}));
        let i=0;
        for (const j of withAngle){
          const delta = (j.load==="empty") ? -(j.lenFt||0) : (j.lenFt||0);
          let placed=false, tries=0;
          while (!placed && tries<K){
            const b=bins[i];
            const jobOK = b.arr.length < maxJobsPerTruck;
            const would = Math.max(0, b.loadFt + (delta>0?delta:0));
            const capOK = (would<=bed) || (j.lenFt||0)===0;
            if (jobOK && capOK){ b.arr.push(j); if (delta>0) b.loadFt+=delta; placed=true; }
            else { i=(i+1)%K; tries++; }
          }
          if (!placed) { const b=bins[i]; if (b.arr.length<maxJobsPerTruck) b.arr.push(j); }
          i=(i+1)%K;
        }
        return bins.map(b=>b.arr);
      }

      const bins = partition(ORIGIN_DEFAULT, feasible, unitsOfType.length, bedFt);

      for (let i=0;i<unitsOfType.length;i++){
        const truck = unitsOfType[i];
        const binAll = bins[i] || [];
        const bin    = binAll.slice(0, maxJobsPerTruck);
        if (!bin.length) continue;

        let origin = ORIGIN_DEFAULT;
        if (bin.some(j=>j.whseFrom)) origin = BAYAMON_WHSE;

        let path = nnOrder(origin, bin);
        path = twoOpt(path);

        let meters=0; for (let k=0;k<path.length-1;k++){
          const a = (path[k].lat!==undefined)? path[k] : path[k].coord;
          const b = (path[k+1].lat!==undefined)? path[k+1] : path[k+1].coord;
          meters += haversineMeters(a,b);
        }
        const miles = meters/1609.344;
        const secs  = meters/((AVERAGE_SPEED_KMH*1000)/3600);
        const urls  = mapsUrlsForOrderedPath(path);

        suggestions.push({
          truck_id: truck.id, driver: driverByTruck.get(truck.id)||null, type, bed_ft: truck.bedFt,
          total_miles: +miles.toFixed(1),
          eta_hmm: `${Math.floor(secs/3600)}:${String(Math.round((secs%3600)/60)).padStart(2,"0")}`,
          maps_urls: urls,
          stops: path.slice(1,-1).map((n,idx)=>({ idx: idx+1, job_id: n.id, tipo: n.tipo||"", servicio: n.servicio||"", lat: n.coord.lat, lng: n.coord.lng }))
        });
      }
    }

    res.json({ generated_at: new Date().toISOString(), origin: ORIGIN_DEFAULT, suggestions });
  }catch(e){
    res.status(500).json({ error: e.message || String(e) });
  }
});

app.listen(PORT, () => console.log(`✅ Route suggester API on :${PORT}`));
