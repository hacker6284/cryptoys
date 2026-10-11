import { mountMicro } from "../shared/micro.js";
import settings from "./settings.js";
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
    title: "Toy chest",
    camera: { position: [0.55, 1.75, 2.35], target: [-1.2, 0.75, 0.55], fov: 40, margin: 1.05 },
    slots: [
        { name: "lidOpen", gapMs: 300, voices: 2 },
        { name: "lidClose", gapMs: 300, voices: 2 },
        { name: "lift", gapMs: 150, voices: 2 },
        { name: "land", gapMs: 120, voices: 3 },
    ],
    frame(ctx) {
        // The chest with its lid open and where the MSG deck lands on the felt.
        const { world } = ctx;
        world.chest.setLid?.(1);
        const box = new ctx.THREE.Box3().setFromObject(world.chest.group);
        world.chest.setLid?.(0);
        const land = world.getTablePose("deck2").position;
        box.expandByPoint(new ctx.THREE.Vector3(land.x + 0.1, land.y + 0.1, land.z + 0.1));
        return box;
    },
    async setup(ctx) {
        sync(ctx);
        director = createToyDirector(ctx.world, DEMOS, { timing });
        ctx.onFrame = (now) => director.update(now);
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
}, settings);
