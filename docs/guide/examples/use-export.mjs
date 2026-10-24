import { total, count, share, StitchwortInputError } from "./export.js";

const basket = [{ name: "tea", pence: 250n }];
console.log(total(basket, { $tag: "PercentOff", percent: 10n }));
console.log(count(basket));

for (const attempt of [() => share(100n, 0n), () => total([{ name: "tea", pence: 250 }], { $tag: "NoDiscount" })]) {
  try {
    attempt();
  } catch (e) {
    console.log(e instanceof StitchwortInputError, e.message);
  }
}
