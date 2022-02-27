export const keys = <T>(x: T) => Object.keys(x) as (keyof T)[];

export const range = (a: number, b?: number) =>
  Array.from({ length: typeof b == "number" ? b - a : a }).map((_, i) => i);

export const unique = <T>(xs: T[]) => Array.from(new Set(xs));

type Falsy = false | 0 | "" | null | undefined;

export const isTruthy = <T>(x: T | Falsy): x is T => !!x;

export const intersperse = <T>(a: T, xs: T[]) =>
  xs.flatMap((x, i) => (i == 0 ? [x] : [a, x]));

export const assertNever = (_: never) => {};
