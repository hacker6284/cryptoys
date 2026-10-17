// Viewer for the doubledeal-grid-deal library entry
// (demos/anim/deck/deal): loops it on the real DoubleDeal table
// code (doubledeal/table.js) laid out at real size on the playroom felt
// (doubledeal/real-layout.js: 63×88 mm cards, the two grids 8 columns ×
// 13 rows, 4 mm gaps). The values are in
// demos/anim/deck/deal/settings.js.
import { ORDER, mountTablePage } from "../../shared/doubledeal-table.js";
import { REAL_LAYOUT } from "../../../doubledeal/real-layout.js";
import { TABLE_TIMING } from "../../../doubledeal/table.js";
import { DEN } from "../../../playroom/constants.js";
import { settings, dealContacts, gridDealVoice } from "../../../anim/deck/deal/index.js";

void mountTablePage({
    id: "doubledeal-grid-deal",
    title: "Deal into the grid",
    voice: gridDealVoice(),
    layout: REAL_LAYOUT,
    frameAll: true,
    frameLift: TABLE_TIMING.liftHop * REAL_LAYOUT.scale, // the cards' hop (101 mm)
    // The dealer's view from the table's near edge, 42° down the 13 rows,
    // fitted in perspective: the whole 8×13 and the packet centred,
    // filling 88 % of the view.
    camera: { position: [DEN.x, 1.672, DEN.z + 1.0], target: [DEN.x, 0.772, DEN.z], fov: 40, fill: 0.88 },
    prepareEach: true,
    // Until the first deal starts (textures loading, sound unlocking): the
    // whole 8×13, the message grid as the deal leaves it.
    opening(table, ctx) {
        table.applyInstant({ kind: ctx.choice("major"), message: ORDER });
    },
    prepare(table, ctx) {
        const kind = ctx.choice("major");
        table.applyInstant({ kind, message: ORDER });
        table.applyInstant({ kind: kind === "deal" ? "scoopcm" : "scooprm" });
    },
    step(ctx, loop, pace) {
        return { step: { kind: ctx.choice("major"), message: ORDER }, contacts: dealContacts(pace) };
    },
}, settings);
