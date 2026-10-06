/**
 * Promise wrapper around worker.js. Replies carry the request id; a
 * caller that only wants the latest answer compares its own generation.
 * If module workers are unavailable the same answer() runs inline.
 */
export function createHasher({ createWorker } = {}) {
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
                const err = new Error(event?.message || "The hash worker failed.");
                for (const job of pending.values()) job.reject(err);
                pending.clear();
            };
        } catch {
            worker = null;
            inline = import("./worker.js");
        }
    }

    function ask(op, bytes) {
        spawn();
        if (inline) return inline.then((mod) => mod.answer({ op, bytes }));
        const id = nextId++;
        return new Promise((resolve, reject) => {
            pending.set(id, { resolve, reject });
            worker.postMessage({ id, op, bytes });
        });
    }

    return {
        digest: (bytes) => ask("digest", bytes),
        show: (bytes) => ask("show", bytes),
        dispose() {
            worker?.terminate?.();
            worker = null;
            pending.clear();
        },
    };
}
