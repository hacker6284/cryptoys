// Viewer for the doubledeal-grid-deal library entry
// (demos/anim/doubledeal-grid-deal): loops it on the real DoubleDeal table
// code (doubledeal/table.js) laid out at real size on the playroom felt
// (doubledeal/real-layout.js: 63×88 mm cards, the two grids 8 columns ×
// 13 rows, 4 mm gaps). The values are in
// demos/anim/doubledeal-grid-deal/settings.js.
import { ORDER, mountTablePage } from "../shared/doubledeal-table.js";
import { REAL_LAYOUT } from "../../doubledeal/real-layout.js";
import { TABLE_TIMING } from "../../doubledeal/table.js";
import { DEN } from "../../playroom/constants.js";
import { settings, dealContacts, gridDealVoice } from "../../anim/doubledeal-grid-deal/index.js";

void mountTablePage({
    id: "doubledeal-grid-deal",
    title: "Deal into the grid",
    voice: gridDealVoice(),
    layout: REAL_LAYOUT,
    frameAll: true,
    frameLift: TABLE_TIMING.liftHop * REAL_LAYOUT.scale, // the cards' hop (101 mm)
    // From the table's near edge, 55° down the 13 rows (kept under the
    // 2.68 m ceiling, so a wider lens).
    camera: { position: [DEN.x, 1.772, DEN.z + 0.7], target: [DEN.x, 0.772, DEN.z], fov: 50, margin: 0.92 },
    frameNear: 0.15,
    prepareEach: true,
    prepare(table, ctx) {
        const kind = ctx.choice("major");
        table.applyInstant({ kind, message: ORDER });
        table.applyInstant({ kind: kind === "deal" ? "scoopcm" : "scooprm" });
    },
    step(ctx, loop, pace) {
        return { step: { kind: ctx.choice("major"), message: ORDER }, contacts: dealContacts(pace) };
    },
}, settings);
