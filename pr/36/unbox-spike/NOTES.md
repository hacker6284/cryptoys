# SPIKE: shelf → unbox → deal

Isolated page. Production DoubleDeal (`?algo=doubledeal`) is unchanged:
shelf box flies, then the live 4×13 table **fades on**. This folder only
asks whether the missing beats — flap, extract, first deal — can feel
high-end inside the existing playroom.

## Preview

- Local: `python3 -m http.server --directory demos` → `/unbox-spike/`
- `?take=physical` (default) · `?take=bloom`
- `?debug=1` shows the current beat name
- `?auto=0` loads the landing shot without playing
- Click / Escape skips after the first lift (same gate as the room)

Production room: still `?algo=doubledeal`.

## What this proves

The playroom already has the hard pieces: `mountWorld`, `toy-director`
lift→arc, pose holds, travel light, `seatOn`. The quality gap is **not**
a new engine. It is three beats that #29 explicitly deferred:

1. **Hold** on the landed box (the fade currently cuts away).
2. **Unbox** the same prop that left the shelf.
3. **Deal** a short packet onto the felt, then pull to the seated lean.

Two takes share the fly and the final eight-card row so the journey is
what changes.

### Take A — physical (recommended)

Tuck box with a hinged flap and a hollow sleeve. After the existing
shelf hold + arc:

- camera eases to a 24° close-up so the 67 mm box is the subject
- a quiet dealer-key lights the cardboard
- flap opens, packet leads a few millimetres, lays down, sleeve recedes
- eight real-face cards hop to a shallow arc (not the 104-card cipher grid)
- lens pulls to the production `doubledeal` lean

This is the Maps model: the toy does the work; chrome stays quiet.

### Take B — bloom

Same fly and seats. The box breathes (emissive + inner point), cards
rise through a dissolving sleeve, fan, settle. Faster and prettier in
stills. Reads as a scene cut — closer to today’s fade, just softer.

## Library eval (GSAP)

Evaluated, **not adopted**.

| | GSAP 3.15 | This spike |
| --- | --- | --- |
| CDN | `https://cdn.jsdelivr.net/npm/gsap@3.15/dist/gsap.min.js` | none |
| License | Standard “no charge” (2025). Free for sites/apps; **not OSI / MIT**. Webflow may revise terms. Prohibited in no-code animation builders that compete with Webflow. | existing rAF + generation (table.js / toy-director) |
| Win | labels, stagger, ease pack, one timeline object | same clock as fly / skip / reduced-motion |
| Cost | second clock next to `director.update`; license note in `assets/LICENSE.md`; another CDN pin besides three / cubing |

The missing quality is **shots, holds, materials, and flap/packet
continuity**, not tween syntax. A production pass should extract the
~80-line `createBeatClock` (or teach `pose-controller` a custom shot)
instead of adding GSAP.

three.js `AnimationMixer` was also skipped: we need skip-to-end and
generation cancels, not clip playback.

## What we would own in production

| Beat | Spike | Production hook |
| --- | --- | --- |
| Shelf hold + fly | `director.borrow` | already shipped (#29 / #25) |
| Camera via shelf → close-up | local `playShot` | add 1–2 named shots or `goTo` custom |
| Unboxable box | `createUnboxRig` | replace `world.makeDeckBox` behind a flag |
| Flap / extract / first deal | `playPhysical` | `adapter.enter` *before* `stageCardTable` fade |
| Live 4×13 table | not here | keep fade or match last packet → `showDecks` |
| Skip / reduced-motion | clock generation | same as fly (snap to seated + laid cards) |

Do **not** write the adopted card-table matrices during unbox. Deal a
stand-in packet, then crossfade or snap to the session table — the
cipher grid is a different scale (`DEAL_SCALE`).

## What looked best

Physical. The bloom stills are prettier; the motion reads as UI. Once
the flap opens and the same cardboard that left the shelf spends a
packet, the room feels like a table. The current production fade is the
bloom take with the unbox deleted.

Holds matter more than extra cards. 300–400 ms of stillness after landing
is what makes the close-up expensive.

## Recommended production path

1. Keep this page as the reference. Do not put it on the hub.
2. Port `createUnboxRig` + `playPhysical` into `playroom/` (new files),
   called from `adapters.doubledeal.enter` **instead of** the box↔table
   crossfade.
3. After the eight-card (or two-packet) open, fade/snap to the existing
   `stageCardTable` session. Do not animate all 104 cipher seats as the
   unbox.
4. Reuse `createBeatClock` — do not add GSAP.
5. Add an `unbox` shot next to `doubledeal` in `poses.js` (or a custom
   `goTo`). Camera stays in the pose controller.
6. Reduced-motion / skip: today’s snap-to-table is fine; optionally use
   bloom’s dissolve as the snap cousin, not the hero path.

**Needs Zach only if** he prefers bloom’s softness as the default. If so,
ship bloom for the enter and keep physical for a later “open the box”
beat. The recommendation is physical as the enter.

## What should NOT ship yet

- This spike in the hub / Maps menu
- GSAP (or any new animation CDN)
- Opening the Kenney chest (lid pivot exists; it is a different toy)
- Two-deck / message+key unbox (TwoDeck-SCM is still later)
- Replacing `makeDeckBox` on `main` without the adapter handoff
- Dealing the live 4×13 / 104-card session as the unbox
- Audio
- Scramble / puzzle / cubing.js changes
- SPEC / `.sudo` / crypto session changes
- Showroom picker chrome, orbit-during-unbox, or a replay control in
  production (Replay is spike-only)

## Risks

1. Hollow sleeve + flap must stay inside the current 67×92×20 mm seat
   or `seatOn` / shelf rings drift.
2. Reparenting cards with `attach` is easy to get wrong on Replay /
   Back. Restow must put every mesh back on the packet.
3. The live table is a different scale. A naive “keep dealing” into
   `createCardTable` will look like a second toy popping on.
4. Close-up FOV 24° is tighter than the seated lean (30°). Hold the
   pull-back until the first cards land or the row reads as a cut.
5. Software-GL / low DPR already caps the room; more transparent cards
   during bloom are the expensive path.

## Out of scope

Wiring `adapter.enter`. Beauty-pass on the production fade. Chest
choreography. Normative SPEC / `.sudo`.

## Browser check (this spike)

Headless SwiftShader is flatter and slower than the shipped room (rAF
starves if we pause to screenshot). What still read clearly:

- Quiet chrome: title, physical/bloom, Replay, research-only note. No
  Maps dock / Message-Key panel.
- Shelf departure: empty deck ring, cube stays put.
- Landed KEY tuck-box with cream flap open (burgundy cardboard, label).
- First card (7♣) hopping onto the felt in front of the same box.

Hold the camera on the fly (`travel`) and only then close up — a tight
unbox shot before the box lands is an empty felt. Packet stays hidden
until the flap moves so we do not flash face cards out of the top.
