export const keys = <T>(x: T) => Object.keys(x) as (keyof T)[];

export const range = (a: number, b?: number) =>
  Array.from({ length: typeof b == "number" ? b - a : a }).map((_, i) => i);

export const unique = <T>(xs: T[]) => Array.from(new Set(xs));
