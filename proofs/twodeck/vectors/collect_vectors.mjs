// Collect TwoDeck known-answer vectors from a sudoc JS build of
// primitives/cipher/twodeck/twodeck.sudo. Do not hand-edit the JSON this
// writes; regenerate with regen.sh.
//
// Usage: node collect_vectors.mjs <sudoc-js-outdir>

import path from "node:path";
import { pathToFileURL } from "node:url";

const outDir = process.argv[2];
if (!outDir) {
  console.error("usage: node collect_vectors.mjs <sudoc-js-outdir>");
  process.exit(1);
}

const impl = await import(pathToFileURL(path.resolve(outDir, "_twodeck_impl.mjs")).href);
const api = await import(pathToFileURL(path.resolve(outDir, "twodeck.mjs")).href);
const rt = await import(pathToFileURL(path.resolve(outDir, "_sudo_rt.mjs")).href);

function host(xs) {
  return rt.host_list(xs, (v) => rt.host_int(v));
}

function cards(xs) {
  return xs.map((x) => rt.int_out(x));
}

function cards2(xss) {
  return xss.map(cards);
}

function eq(a, b) {
  return JSON.stringify(a) === JSON.stringify(b);
}

function assert(cond, msg) {
  if (!cond) throw new Error(msg);
}

const identity = Array.from({ length: 52 }, (_, i) => i);
const reverse = Array.from({ length: 52 }, (_, i) => 51 - i);
const mul17 = Array.from({ length: 52 }, (_, i) => (i * 17) % 52);

// Published encrypt/decrypt KAT from twodeck.sudo "decrypt undoes encrypt".
const publishedMessage = [
  0, 32, 38, 42, 13, 19, 17, 5, 41, 25, 48, 6, 31, 44, 3, 16, 7, 4, 34, 40, 18,
  49, 14, 51, 20, 46, 28, 11, 10, 15, 45, 43, 2, 26, 22, 8, 37, 33, 12, 35, 24,
  50, 39, 30, 21, 1, 27, 47, 36, 23, 29, 9,
];
const publishedKey = [
  48, 42, 25, 26, 3, 37, 39, 50, 11, 2, 43, 8, 10, 7, 40, 38, 34, 0, 49, 51, 22,
  27, 23, 9, 12, 15, 44, 41, 21, 28, 20, 13, 19, 14, 45, 31, 35, 18, 17, 30, 6,
  36, 47, 16, 1, 33, 29, 5, 46, 32, 24, 4,
];
const publishedCipher = [
  49, 48, 9, 39, 29, 37, 22, 0, 16, 44, 24, 43, 8, 23, 33, 14, 12, 17, 41, 4, 19,
  46, 34, 26, 50, 13, 51, 20, 10, 28, 1, 35, 6, 7, 38, 31, 47, 36, 5, 30, 3, 27,
  11, 2, 18, 42, 15, 40, 25, 32, 45, 21,
];

const identityNonce = Array.from({ length: 39 }, (_, i) => i);
const reverseNonce = Array.from({ length: 39 }, (_, i) => 38 - i);

function passkey(d) {
  return cards(impl.passkey(host(d)));
}
function expandKeys(k0) {
  return cards2(impl.expand_keys(host(k0)));
}
function mixColumns(d) {
  return cards(impl.mix_columns(host(d)));
}
function sumRanks(d) {
  return cards(impl.scoop_cm(impl.sum_ranks(impl.lay_cm(host(d)))));
}
function shiftRows(d) {
  return cards(impl.scoop_cm(impl.shift_rows(impl.lay_cm(host(d)))));
}
function unkeyedFull(d) {
  return cards(impl.unkeyed_full(host(d)));
}
function compose(m, k) {
  return cards(impl.compose(host(m), host(k)));
}
function encrypt(m, k) {
  return api.encrypt(m, k);
}
function decrypt(c, k) {
  return api.decrypt(c, k);
}
function counterDeck(nonce, index) {
  return api.counter_deck(nonce, index);
}

const gotPublished = encrypt(publishedMessage, publishedKey);
assert(
  eq(gotPublished, publishedCipher),
  `published encrypt mismatch:\n got ${JSON.stringify(gotPublished)}\n want ${JSON.stringify(publishedCipher)}`,
);
assert(eq(decrypt(publishedCipher, publishedKey), publishedMessage), "published decrypt mismatch");

const vectors = [];

function add(v) {
  vectors.push(v);
}

add({
  name: "encrypt_published",
  kind: "encrypt",
  source: "twodeck.sudo test \"decrypt undoes encrypt\"",
  message: publishedMessage,
  key: publishedKey,
  cipher: publishedCipher,
});

for (const [name, message, key] of [
  ["encrypt_identity_identity", identity, identity],
  ["encrypt_reverse_identity", reverse, identity],
  ["encrypt_identity_published", identity, publishedKey],
  ["encrypt_mul17_published", mul17, publishedKey],
  ["encrypt_reverse_reverse", reverse, reverse],
]) {
  const cipher = encrypt(message, key);
  assert(eq(decrypt(cipher, key), message), `${name} round-trip failed`);
  add({ name, kind: "encrypt", source: "sudoc JS extra KAT", message, key, cipher });
}

for (const [name, input] of [
  ["passkey_identity", identity],
  ["passkey_reverse", reverse],
  ["passkey_published_key", publishedKey],
  ["passkey_mul17", mul17],
]) {
  add({ name, kind: "passkey", source: "sudoc JS (passkey export via impl)", input, output: passkey(input) });
}

add({
  name: "expand_keys_published",
  kind: "expand_keys",
  source: "sudoc JS expand_keys on the published test key",
  k0: publishedKey,
  keys: expandKeys(publishedKey),
});
add({
  name: "expand_keys_identity",
  kind: "expand_keys",
  source: "sudoc JS expand_keys on the identity deck",
  k0: identity,
  keys: expandKeys(identity),
});

for (const [name, nonce, index] of [
  ["counter_deck_identity_0", identityNonce, 0],
  ["counter_deck_identity_1", identityNonce, 1],
  ["counter_deck_identity_2", identityNonce, 2],
  ["counter_deck_identity_12", identityNonce, 12],
  ["counter_deck_reverse_0", reverseNonce, 0],
  ["counter_deck_reverse_1", reverseNonce, 1],
]) {
  add({
    name,
    kind: "counter_deck",
    source: name.startsWith("counter_deck_identity")
      ? "twodeck.sudo test \"counter rail keeps the nonce and permutes diamonds\""
      : "twodeck.sudo test \"ecb repeats a block and ctr does not\" (nonce)",
    nonce,
    index,
    deck: counterDeck(nonce, index),
  });
}

for (const [name, input] of [
  ["mix_columns_identity", identity],
  ["mix_columns_reverse", reverse],
  ["mix_columns_mul17", mul17],
]) {
  add({
    name,
    kind: "mix_columns",
    source: name === "mix_columns_reverse" ? "twodeck.sudo test \"grid cycle inverts\"" : "sudoc JS extra layer KAT",
    input,
    output: mixColumns(input),
  });
}

add({
  name: "sum_ranks_mul17",
  kind: "sum_ranks",
  source: "twodeck.sudo test \"sum ranks and shift rows invert\"",
  input: mul17,
  output: sumRanks(mul17),
});
add({
  name: "shift_rows_mul17",
  kind: "shift_rows",
  source: "twodeck.sudo test \"sum ranks and shift rows invert\"",
  input: mul17,
  output: shiftRows(mul17),
});

for (const [name, input] of [
  ["unkeyed_full_identity", identity],
  ["unkeyed_full_reverse", reverse],
  ["unkeyed_full_mul17", mul17],
]) {
  add({ name, kind: "unkeyed_full", source: "sudoc JS extra layer KAT", input, output: unkeyedFull(input) });
}

add({
  name: "compose_identity_reverse_key",
  kind: "compose",
  source: "twodeck.sudo test \"compose inverts and passkey keeps the deck\"",
  message: identity,
  key: reverse,
  output: compose(identity, reverse),
});
add({
  name: "compose_published",
  kind: "compose",
  source: "sudoc JS extra layer KAT",
  message: publishedMessage,
  key: publishedKey,
  output: compose(publishedMessage, publishedKey),
});

const ctrBlocks = [publishedMessage, publishedMessage];
const ctrOut = api.ctr_encrypt(ctrBlocks, publishedKey, reverseNonce);
assert(!eq(ctrOut[0], ctrOut[1]), "CTR should not repeat a block");
assert(eq(api.ctr_decrypt(ctrOut, publishedKey, reverseNonce), ctrBlocks), "CTR decrypt mismatch");
add({
  name: "ctr_encrypt_published_repeat",
  kind: "ctr_encrypt",
  source: "twodeck.sudo test \"ecb repeats a block and ctr does not\"",
  blocks: ctrBlocks,
  key: publishedKey,
  nonce: reverseNonce,
  output: ctrOut,
});

const doc = {
  schema: 1,
  generated_by: "proofs/twodeck/vectors/regen.sh",
  source: "primitives/cipher/twodeck/twodeck.sudo",
  note:
    "Known-answer vectors from the sudo tests plus extras evaluated by the sudoc JS target. " +
    "Evidence that the Lean model agrees with twodeck.sudo on these inputs — not a proof that the sudo text equals the Lean model.",
  decks_are: "52-element arrays of CHaSeD card ids (0..51)",
  vectors,
};

process.stdout.write(JSON.stringify(doc, null, 2) + "\n");
