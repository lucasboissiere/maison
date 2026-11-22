// Lit les calendriers iCloud publiés, calcule les rendez-vous des 60 prochains jours
// et les écrit CHIFFRÉS dans agenda.json (AES-256-GCM, clé = SHA-256 de la clé secrète).
// Lancé par GitHub Actions (.github/workflows/agenda.yml) avec les secrets CLE et CALENDRIERS.
import { createHash, createCipheriv, randomBytes } from "node:crypto";
import { readFileSync, writeFileSync } from "node:fs";

const FUSEAU = "Europe/Paris";
const JOURS_FENETRE = 60;
const JOUR = 864e5;

// ───────── Lecture des fichiers .ics ─────────
// Toutes les heures sont ramenées à l'heure de Paris, stockées comme des dates « UTC naïves »
// (les champs UTC de la Date = l'heure murale à Paris).

const fmtParis = new Intl.DateTimeFormat("en-GB", {
  timeZone: FUSEAU, year: "numeric", month: "2-digit", day: "2-digit",
  hour: "2-digit", minute: "2-digit", second: "2-digit", hourCycle: "h23",
});

function versParis(msUtc) {
  const p = {};
  for (const x of fmtParis.formatToParts(new Date(msUtc))) p[x.type] = x.value;
  return Date.UTC(+p.year, +p.month - 1, +p.day, +p.hour, +p.minute, +p.second);
}

function lireDate(valeur, params) {
  const v = valeur.trim();
  const m = /^(\d{4})(\d{2})(\d{2})(?:T(\d{2})(\d{2})(\d{2})(Z)?)?$/.exec(v);
  if (!m) return null;
  if (!m[4] || /VALUE=DATE(?!-)/i.test(params)) {
    return { ms: Date.UTC(+m[1], +m[2] - 1, +m[3]), jour: true };
  }
  const naif = Date.UTC(+m[1], +m[2] - 1, +m[3], +m[4], +m[5], +m[6]);
  return { ms: m[7] ? versParis(naif) : naif, jour: false };
}

function lireDuree(v) {
  const m = /^([+-])?P(?:(\d+)W)?(?:(\d+)D)?(?:T(?:(\d+)H)?(?:(\d+)M)?(?:(\d+)S)?)?$/.exec(v.trim());
  if (!m) return 0;
  const s = ((+m[2] || 0) * 7 + (+m[3] || 0)) * JOUR + ((+m[4] || 0) * 3600 + (+m[5] || 0) * 60 + (+m[6] || 0)) * 1000;
  return m[1] === "-" ? -s : s;
}

function lireEvenements(texte) {
  const lignes = texte.replace(/\r\n/g, "\n").replace(/\n[ \t]/g, "").split("\n");
  const res = [];
  let cur = null, profondeur = 0;
  for (const ligne of lignes) {
    if (ligne === "BEGIN:VEVENT") { cur = { exdates: [] }; profondeur = 0; continue; }
    if (!cur) continue;
    if (ligne.startsWith("BEGIN:")) { profondeur++; continue; }   // VALARM…
    if (ligne.startsWith("END:") && ligne !== "END:VEVENT") { profondeur--; continue; }
    if (ligne === "END:VEVENT") { res.push(cur); cur = null; continue; }
    if (profondeur > 0) continue;
    const i = ligne.indexOf(":");
    if (i < 0) continue;
    const tete = ligne.slice(0, i), valeur = ligne.slice(i + 1);
    const nom = tete.split(";")[0].toUpperCase();
    const params = tete.slice(nom.length);
    switch (nom) {
      case "SUMMARY": cur.titre = texteIcs(valeur); break;
      case "LOCATION": cur.lieu = texteIcs(valeur).split("\n")[0]; break;
      case "UID": cur.uid = valeur; break;
      case "STATUS": cur.statut = valeur.toUpperCase(); break;
      case "DTSTART": cur.debut = lireDate(valeur, params); break;
      case "DTEND": cur.fin = lireDate(valeur, params); break;
      case "DURATION": cur.duree = lireDuree(valeur); break;
      case "RRULE": cur.regle = valeur; break;
      case "RECURRENCE-ID": cur.remplace = lireDate(valeur, params); break;
      case "EXDATE":
        for (const x of valeur.split(",")) { const d = lireDate(x, params); if (d) cur.exdates.push(d.ms); }
        break;
    }
  }
  return res;
}

function texteIcs(v) {
  return v.replace(/\\n/gi, "\n").replace(/\\([,;\\])/g, "$1").trim();
}

// ───────── Répétitions (RRULE) ─────────

const CODES_JOURS = ["SU", "MO", "TU", "WE", "TH", "FR", "SA"];

function nemeJourDuMois(annee, mois, jourSemaine, n) {
  // n = 1, 2… ou -1 (dernier)
  if (n > 0) {
    const premier = new Date(Date.UTC(annee, mois, 1)).getUTCDay();
    const jour = 1 + ((jourSemaine - premier + 7) % 7) + (n - 1) * 7;
    const d = Date.UTC(annee, mois, jour);
    return new Date(d).getUTCMonth() === mois ? d : null;
  }
  const dernier = new Date(Date.UTC(annee, mois + 1, 0));
  const jour = dernier.getUTCDate() - ((dernier.getUTCDay() - jourSemaine + 7) % 7) + (n + 1) * 7;
  return jour > 0 ? Date.UTC(annee, mois, jour) : null;
}

function occurrences(ev, finFenetre) {
  const debut = ev.debut.ms;
  if (!ev.regle) return [debut];
  const r = {};
  for (const p of ev.regle.split(";")) { const [k, v] = p.split("="); r[k.toUpperCase()] = v; }
  const pas = Math.max(1, parseInt(r.INTERVAL || "1", 10));
  const nombre = r.COUNT ? parseInt(r.COUNT, 10) : Infinity;
  let jusqua = Infinity;
  if (r.UNTIL) { const u = lireDate(r.UNTIL, ""); if (u) jusqua = u.jour ? u.ms + JOUR - 1 : u.ms; }
  const limite = Math.min(finFenetre, jusqua);
  const heure = debut % JOUR;
  const d0 = new Date(debut);
  const res = [];
  let n = 0;
  const ajouter = (ms) => {
    if (ms < debut) return true;
    if (ms > limite || n >= nombre) return false;
    n++; res.push(ms); return true;
  };
  const jours = r.BYDAY ? r.BYDAY.split(",").map((x) => {
    const m = /^([+-]?\d+)?([A-Z]{2})$/.exec(x.trim());
    return m ? { n: m[1] ? parseInt(m[1], 10) : 0, j: CODES_JOURS.indexOf(m[2]) } : null;
  }).filter((x) => x && x.j >= 0) : [];
  const joursMois = r.BYMONTHDAY ? r.BYMONTHDAY.split(",").map((x) => parseInt(x, 10)) : [];

  for (let k = 0; k < 5000; k++) {
    let candidats = [];
    if (r.FREQ === "DAILY") {
      candidats = [debut + k * pas * JOUR];
    } else if (r.FREQ === "WEEKLY") {
      const lundi = debut - ((d0.getUTCDay() + 6) % 7) * JOUR - heure + k * pas * 7 * JOUR;
      const liste = jours.length ? jours.map((x) => (x.j + 6) % 7) : [(d0.getUTCDay() + 6) % 7];
      candidats = liste.sort((a, b) => a - b).map((i) => lundi + i * JOUR + heure);
    } else if (r.FREQ === "MONTHLY") {
      const total = d0.getUTCMonth() + k * pas;
      const a = d0.getUTCFullYear() + Math.floor(total / 12), m = total % 12;
      if (jours.length) {
        candidats = jours.map((x) => nemeJourDuMois(a, m, x.j, x.n || 1)).filter((x) => x !== null).map((x) => x + heure);
      } else {
        const dates = joursMois.length ? joursMois : [d0.getUTCDate()];
        candidats = dates.map((j) => Date.UTC(a, m, j)).filter((x) => new Date(x).getUTCMonth() === m).map((x) => x + heure);
      }
      candidats.sort((x, y) => x - y);
    } else if (r.FREQ === "YEARLY") {
      const a = d0.getUTCFullYear() + k * pas;
      const mois = r.BYMONTH ? r.BYMONTH.split(",").map((x) => parseInt(x, 10) - 1) : [d0.getUTCMonth()];
      for (const m of mois) {
        if (jours.length) {
          for (const x of jours) { const d = nemeJourDuMois(a, m, x.j, x.n || 1); if (d !== null) candidats.push(d + heure); }
        } else {
          const j = joursMois.length ? joursMois : [d0.getUTCDate()];
          for (const jj of j) { const d = Date.UTC(a, m, jj); if (new Date(d).getUTCMonth() === m) candidats.push(d + heure); }
        }
      }
      candidats.sort((x, y) => x - y);
    } else {
      return [debut];
    }
    let continuer = true;
    for (const c of candidats) { if (!ajouter(c)) { continuer = false; break; } }
    if (!continuer) break;
    if (candidats.length && candidats[0] > limite) break;
  }
  return res;
}

// ───────── Calcul de l'agenda ─────────

function isoJour(ms) { return new Date(ms).toISOString().slice(0, 10); }
function isoHeure(ms) { return new Date(ms).toISOString().slice(11, 16); }

function calculer(textes, maintenantUtc) {
  const maintenant = versParis(maintenantUtc);
  const debutFenetre = maintenant - (maintenant % JOUR);
  const finFenetre = debutFenetre + JOURS_FENETRE * JOUR;
  const tous = [];
  for (const t of textes) if (t) tous.push(...lireEvenements(t));

  // Occurrences modifiées une par une (RECURRENCE-ID)
  const modifiees = {};
  for (const e of tous) if (e.remplace && e.uid) (modifiees[e.uid] = modifiees[e.uid] || new Set()).add(e.remplace.ms);

  const sortie = [];
  const vus = new Set();
  for (const e of tous) {
    if (!e.debut || e.statut === "CANCELLED") continue;
    const duree = e.fin ? e.fin.ms - e.debut.ms : (e.duree || (e.debut.jour ? JOUR : 0));
    const exclues = new Set(e.exdates);
    const remplacees = (!e.remplace && e.uid && modifiees[e.uid]) || new Set();
    for (const s of occurrences(e, finFenetre)) {
      if (exclues.has(s) || remplacees.has(s)) continue;
      const f = s + Math.max(duree, 0);
      if (s >= finFenetre || (f <= debutFenetre && s < debutFenetre)) continue;
      if (f <= debutFenetre && duree > 0) continue;
      const base = { t: e.titre || "(sans titre)", l: e.lieu || "" };
      if (e.debut.jour) {
        // Journée entière : affichée sur chaque jour couvert
        for (let j = Math.max(s, debutFenetre); j < Math.max(f, s + JOUR) && j < finFenetre; j += JOUR) {
          const cle = "j" + j + base.t;
          if (vus.has(cle)) continue;
          vus.add(cle);
          sortie.push(Object.assign({ d: isoJour(j), h: null, j: true }, base));
        }
      } else {
        const jourAffiche = s < debutFenetre ? debutFenetre : s;
        const cle = "h" + s + base.t;
        if (vus.has(cle)) continue;
        vus.add(cle);
        sortie.push(Object.assign({ d: isoJour(jourAffiche), h: s < debutFenetre ? "" : isoHeure(s), f: isoHeure(f), j: false }, base));
      }
    }
  }
  sortie.sort((a, b) => (a.d < b.d ? -1 : a.d > b.d ? 1 : (a.j === b.j ? ((a.h || "") < (b.h || "") ? -1 : 1) : a.j ? -1 : 1)));
  return sortie;
}

// ───────── Programme principal ─────────

const CLE = process.env.CLE || "";
const liens = String(process.env.CALENDRIERS || "").split(/[\s,]+/).filter(Boolean)
  .map((l) => l.replace(/^webcal:/i, "https:"));
if (!CLE || !liens.length) { console.error("Secrets CLE ou CALENDRIERS manquants"); process.exit(1); }

const textes = await Promise.all(liens.map((l) =>
  fetch(l).then((r) => (r.ok ? r.text() : "")).catch(() => "")));
if (!textes.some(Boolean)) { console.error("Aucun calendrier n'a pu être lu"); process.exit(1); }

const clair = JSON.stringify({ ev: calculer(textes, Date.now()) });
const h = createHash("sha256").update(CLE + "|" + clair).digest("hex").slice(0, 16);

let ancien = {};
try { ancien = JSON.parse(readFileSync("agenda.json", "utf8")); } catch (e) { /* premier passage */ }
const age = Date.now() - (Date.parse(ancien.maj || "") || 0);
if (ancien.h === h && age < 20 * 3600e3) { console.log("Agenda inchangé"); process.exit(0); }

const cle = createHash("sha256").update(CLE, "utf8").digest();
const iv = randomBytes(12);
const c = createCipheriv("aes-256-gcm", cle, iv);
const d = Buffer.concat([c.update(clair, "utf8"), c.final(), c.getAuthTag()]);
writeFileSync("agenda.json", JSON.stringify({ v: 1, maj: new Date().toISOString(), h, i: iv.toString("base64"), d: d.toString("base64") }) + "\n");
console.log("Agenda mis à jour : " + textes.filter(Boolean).length + " calendrier(s)");
