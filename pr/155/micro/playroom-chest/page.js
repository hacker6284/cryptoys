import { mountMicro } from "../shared/micro.js";
import { DEN } from "../../playroom/constants.js";
import { DIRECTOR_TIMING, createToyDirector } from "../../playroom/toy-director.js";

// The DoubleDeal borrow/home choreography from playroom/toy-director.js:
// chest lid opens, the MSG deck flies out of the toy chest onto the felt
// (FLY_MS − 200) while the KEY deck flies off the shelf (FLY_MS), lid
// closes; home reverses it into the chest and onto the shelf.
const DEMOS = { doubledeal: { toys: ["deck", "deck2"], chest: true } };
const timing = { ...DIRECTOR_TIMING };
let director = null;

function sync(ctx) {
    for (const k of Object.keys(timing)) timing[k] = ctx.timing(k);
}

void mountMicro({
    id: "playroom-chest",
    title: "Toy chest: lid and a toy flying out",
    summary: "The toy chest lid opens, the MSG deck flies out onto the felt (and the KEY deck off the shelf), the lid closes; or the reverse.",
    source: "playroom/toy-director.js borrow / home / lid (DIRECTOR_TIMING) · world.js chest",
    camera: { position: [0.55, 1.75, 2.35], target: [-1.2, 0.75, 0.55], fov: 46 },
    loopGapMs: 1200,
    choices: [{ key: "mode", label: "Loop", value: "borrow", options: [["lid", "lid opens and closes"], ["borrow", "out of the chest (borrow)"], ["home", "back into the chest (home)"], ["both", "out, then back"]] }],
    timing: [
        { key: "LID_OPEN_MS", label: "LID_OPEN_MS", min: 100, max: 2000, step: 10, value: DIRECTOR_TIMING.LID_OPEN_MS, unit: " ms" },
        { key: "LID_CLOSE_MS", label: "LID_CLOSE_MS", min: 100, max: 2000, step: 10, value: DIRECTOR_TIMING.LID_CLOSE_MS, unit: " ms" },
        { key: "FLY_MS", label: "FLY_MS", min: 400, max: 4000, step: 20, value: DIRECTOR_TIMING.FLY_MS, unit: " ms" },
        { key: "LIFT_MS", label: "LIFT_MS", min: 0, max: 1200, step: 10, value: DIRECTOR_TIMING.LIFT_MS, unit: " ms" },
    ],
    slots: [
        { name: "lidOpen", label: "Lid opens (creak)", contact: "the lid starts to open", from: [["unbox", "chest-lid-open"]], gapMs: 300, voices: 2 },
        { name: "lidClose", label: "Lid closes", contact: "the lid shuts", from: [["unbox", "chest-lid-close"]], gapMs: 300, voices: 2 },
        { name: "lift", label: "Toy lifts off", contact: "a toy leaves its seat", from: ["playroom-fly"], gapMs: 150, voices: 2, off: true },
        { name: "land", label: "Toy lands", contact: "a toy lands (felt, shelf or chest)", from: [["unbox", "box-setdown-felt"]], gapMs: 120, voices: 3 },
    ],
    async setup(ctx) {
        sync(ctx);
        director = createToyDirector(ctx.world, DEMOS, { timing });
        ctx.onFrame = (now) => director.update(now);
    },
    onTiming(ctx) {
        sync(ctx);
    },
    stop() {
        director?.skip();
    },
    async reset(ctx) {
        director.skip();
        await director.home({ snap: true });
        ctx.world.setChestLid?.(0);
    },
    async cycle(ctx) {
        sync(ctx);
        const mode = ctx.choice("mode");
        const T = timing;
        const run = async (what) => {
            const gen = ctx.alive;
            const contacts = [];
            if (what === "lid") contacts.push(["lidOpen", 0], ["lidClose", T.LID_OPEN_MS + 400 + T.LID_CLOSE_MS]);
            if (what === "borrow") {
                contacts.push(["lidOpen", 0], ["lift", 0], ["lift", T.LID_OPEN_MS]);
                contacts.push(["land", T.FLY_MS], ["land", T.LID_OPEN_MS + T.FLY_MS - 200]);
                contacts.push(["lidClose", T.LID_OPEN_MS + T.FLY_MS - 200 + T.LID_CLOSE_MS]);
            }
            if (what === "home") {
                contacts.push(["lidOpen", 0], ["lift", T.LID_OPEN_MS], ["land", T.LID_OPEN_MS + T.FLY_MS]);
                contacts.push(["lidClose", T.LID_OPEN_MS + T.FLY_MS + T.LID_CLOSE_MS]);
            }
            const lead = ctx.leadIn(contacts);
            if (lead && !(await ctx.wait(lead))) return false;
            if (gen !== ctx.alive) return false;
            const t0 = performance.now();
            for (const [slot, at] of contacts) ctx.contact(slot, t0 + at);
            if (what === "lid") {
                await director.lid(1);
                if (!(await ctx.wait(400))) return false;
                await director.lid(0);
            } else if (what === "borrow") {
                await director.borrow("doubledeal");
                // borrow resolves when the KEY deck lands; the lid may still be closing.
                await ctx.wait(Math.max(0, T.LID_OPEN_MS + T.FLY_MS - 200 + T.LID_CLOSE_MS - T.FLY_MS) + 30);
            } else {
                await director.home();
            }
            return gen === ctx.alive;
        };
        if (mode === "lid") return void (await run("lid"));
        if (mode === "home") {
            await director.borrow("doubledeal", { snap: true });
            director.skip();
            if (!(await ctx.wait(500))) return;
            return void (await run("home"));
        }
        await this.reset(ctx);
        if (!(await run("borrow"))) return;
        if (mode === "both") {
            if (!(await ctx.wait(ctx.settings.loopGapMs))) return;
            await run("home");
        }
    },
    config(ctx) {
        sync(ctx);
        return {
            demo: "playroom",
            paste: "constants → demos/playroom/constants.js; sounds → a demos/shared/sound.js table (offsetMs is relative to each contact)",
            constants: { ...timing },
        };
    },
});
