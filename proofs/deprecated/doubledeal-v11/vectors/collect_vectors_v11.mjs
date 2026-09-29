// FROZEN DoubleDeal v11 (superseded). Collects the v11 known-answer vectors from a
// sudoc JS build of primitives/cipher/doubledeal/v11/doubledeal_v11.sudo. This is
// proofs/doubledeal/vectors/collect_vectors.mjs as of the v11 freeze, with the v11
// module names and v11 provenance fields; the vector list is unchanged. Do not
// hand-edit the JSON this writes; regenerate with proofs/doubledeal/vectors/regen.sh v11.
//
// Usage: node collect_vectors.mjs <sudoc-js-outdir>

import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const outDir = process.argv[2];
if (!outDir) {
  console.error("usage: node collect_vectors.mjs <sudoc-js-outdir>");
  process.exit(1);
}

const impl = await import(pathToFileURL(path.resolve(outDir, "_doubledeal_v11_impl.mjs")).href);
const api = await import(pathToFileURL(path.resolve(outDir, "doubledeal_v11.mjs")).href);
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

// Published encrypt/decrypt KAT: message, key and cipher are read from the
// doubledeal.sudo test "decrypt undoes encrypt" (no second hand-kept copy).
// publishedCipher is then computed with the JS target and asserted equal to
// the test's cipher below.
const sudoPath =
  process.env.DOUBLEDEAL_SUDO ||
  path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../../../../primitives/cipher/doubledeal/v11/doubledeal_v11.sudo");

function publishedTestDecks(sudoText) {
  const start = sudoText.indexOf('test "decrypt undoes encrypt"');
  assert(start >= 0, `no test "decrypt undoes encrypt" in ${sudoPath}`);
  const next = sudoText.indexOf("\ntest ", start + 1);
  const body = sudoText.slice(start, next < 0 ? undefined : next);
  const deck = (name) => {
    const m = body.match(new RegExp(`^\\s+${name} = \\[([0-9, ]+)\\]`, "m"));
    assert(m, `test "decrypt undoes encrypt": no ${name} literal`);
    return m[1].split(",").map((x) => Number(x.trim()));
  };
  return { message: deck("message"), key: deck("key"), cipher: deck("cipher") };
}

const publishedTest = publishedTestDecks(readFileSync(sudoPath, "utf8"));
const publishedMessage = publishedTest.message;
const publishedKey = publishedTest.key;

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

const publishedCipher = encrypt(publishedMessage, publishedKey);
assert(
  eq(publishedCipher, publishedTest.cipher),
  `published encrypt mismatch with the sudo test:\n got ${JSON.stringify(publishedCipher)}\n want ${JSON.stringify(publishedTest.cipher)}`,
);
assert(eq(decrypt(publishedCipher, publishedKey), publishedMessage), "published decrypt mismatch");

const vectors = [];

function add(v) {
  vectors.push(v);
}

add({
  name: "encrypt_published",
  kind: "encrypt",
  source: "doubledeal.sudo test \"decrypt undoes encrypt\"",
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
      ? "doubledeal.sudo test \"counter rail keeps the nonce and permutes diamonds\""
      : "doubledeal.sudo test \"ecb repeats a block and ctr does not\" (nonce)",
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
    source: name === "mix_columns_reverse" ? "doubledeal.sudo test \"grid cycle inverts\"" : "sudoc JS extra layer KAT",
    input,
    output: mixColumns(input),
  });
}

add({
  name: "sum_ranks_mul17",
  kind: "sum_ranks",
  source: "doubledeal.sudo test \"sum ranks and shift rows invert\"",
  input: mul17,
  output: sumRanks(mul17),
});
add({
  name: "shift_rows_mul17",
  kind: "shift_rows",
  source: "doubledeal.sudo test \"sum ranks and shift rows invert\"",
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
  source: "doubledeal.sudo test \"compose inverts and passkey keeps the deck\"",
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
  source: "doubledeal.sudo test \"ecb repeats a block and ctr does not\"",
  blocks: ctrBlocks,
  key: publishedKey,
  nonce: reverseNonce,
  output: ctrOut,
});

const sudoSha = process.env.DOUBLEDEAL_SUDO_SHA256;
const sudocodeCommit = process.env.SUDOCODE_COMMIT;
if (!sudoSha || !sudocodeCommit) {
  console.error(
    "collect_vectors.mjs: set DOUBLEDEAL_SUDO_SHA256 and SUDOCODE_COMMIT (regen.sh does this)",
  );
  process.exit(1);
}

const doc = {
  schema: 1,
  generated_by: "proofs/doubledeal/vectors/regen.sh v11",
  source: "primitives/cipher/doubledeal/v11/doubledeal_v11.sudo",
  sudo_sha256: sudoSha,
  sudocode_commit: sudocodeCommit,
  note:
    "Known-answer vectors from the sudo tests plus extras evaluated by the sudoc JS target. " +
    "Evidence that the Lean model agrees with doubledeal.sudo on these inputs — not a proof that the sudo text equals the Lean model.",
  decks_are: "52-element arrays of CHaSeD card ids (0..51)",
  vectors,
};

// Pin the serializer: escape non-ASCII so the note's em dash stays \u2014
// (the escaped form the vectors were first committed with, before v9).
const asciiJson = (v) =>
  JSON.stringify(v, null, 2).replace(/[\u007f-\uffff]/g, (c) => "\\u" + c.charCodeAt(0).toString(16).padStart(4, "0"));
process.stdout.write(asciiJson(doc) + "\n");
