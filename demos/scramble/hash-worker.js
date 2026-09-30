import { hashMessage } from "./hash.js";

self.onmessage = ({ data: { version, bytes } }) => self.postMessage(hashMessage(version, bytes));
