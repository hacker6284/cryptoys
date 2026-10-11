/**
 * Promise wrapper around worker.js (as megadreifach/hasher.js). If module
 * workers are unavailable the same answer() runs inline.
 */
export function createKeys({ createWorker } = {}) {
    let worker = null;
    let inline = null;
    let nextId = 1;
    const pending = new Map();

    function spawn() {
        if (worker || inline) return;
        try {
            worker = createWorker
                ? createWorker()
                : new Worker(new URL("./worker.js", import.meta.url), { type: "module" });
            worker.onmessage = ({ data }) => {
                const job = pending.get(data.id);
                if (!job) return;
                pending.delete(data.id);
                if (data.error) job.reject(new Error(data.error));
                else job.resolve(data);
            };
            worker.onerror = (event) => {
                const err = new Error(event?.message || "The BS worker failed.");
                for (const job of pending.values()) job.reject(err);
                pending.clear();
            };
        } catch {
            worker = null;
            inline = import("./worker.js");
        }
    }

    function ask(message) {
        spawn();
        if (inline) return inline.then((mod) => mod.answer(message));
        const id = nextId++;
        return new Promise((resolve, reject) => {
            pending.set(id, { resolve, reject });
            worker.postMessage({ id, ...message });
        });
    }

    return {
        show: (seed) => ask({ op: "show", seed }),
        showVector: (vector) => ask({ op: "show", vector }),
        check: (vector) => ask({ op: "check", vector }),
        /** One step's peg moves (generated step_moves) in the last show. */
        moves: (step) => ask({ op: "moves", step }),
        dispose() {
            worker?.terminate?.();
            worker = null;
            pending.clear();
        },
    };
}
