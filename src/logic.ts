import { intersperse, isTruthy, range, unique } from "./utils";

const RULES = [
  "Boole",
  "Imp_I",
  "Imp_E",
  "Dis_E",
  "Dis_I1",
  "Dis_I2",
  "Con_I",
  "Con_E1",
  "Con_E2",
  "Uni_I",
  "Uni_E",
  "Exi_I",
  "Exi_E",
] as const;
export type Rule = typeof RULES[number];
const createRule = <
  Args = void,
  T extends true | keyof Terms | ((term: Term) => boolean) = (
    term: Term
  ) => boolean
>(
  canApply: T,
  apply: (
    step: Omit<Step, "goal"> & {
      goal: T extends keyof Terms ? Terms[T] & { type: T } : Term;
    },
    args: Args
  ) => [Term[], Term][] | { steps: [Term[], Term][]; intros: Term },
  options?: (step: Step) => [string, Args][]
): {
  canApply: (term: Term) => boolean;
  apply: (step: Step, args: Args) => { steps: Step[]; intros: Term | void };
  options?: (step: Step) => [string, Args][];
} => ({
  canApply:
    typeof canApply == "string"
      ? (t) => t.type == canApply
      : typeof canApply == "function"
      ? canApply
      : (_) => true,
  apply: (step, args) => {
    const res = apply(step as any, args);
    const steps = Array.isArray(res) ? res : res.steps;
    const intros = Array.isArray(res) ? void 0 : res.intros;
    return {
      intros,
      steps: steps.map<Step>(([assumptions, goal]) => ({
        rule: null,
        assumptions: [...assumptions, ...step.assumptions],
        goal,
      })),
    };
  },
  options,
});
const applyRule = {
  Boole: createRule(true, (step) => [[[imp(step.goal, falsity())], falsity()]]),
  Imp_I: createRule("imp", (step) => [[[step.goal.a], step.goal.b]]),
  Imp_E: createRule(true, (step) => {
    const h = hole();
    return [
      [[], imp(h, step.goal)],
      [[], h],
    ];
  }),
  Dis_E: createRule(true, (step) => {
    const a = hole();
    const b = hole();
    return [
      [[], dis(a, b)],
      [[a], step.goal],
      [[b], step.goal],
    ];
  }),
  Dis_I1: createRule("dis", (step) => {
    return [[[], step.goal.a]];
  }),
  Dis_I2: createRule("dis", (step) => {
    return [[[], step.goal.b]];
  }),
  Con_I: createRule("con", (step) => [
    [[], step.goal.a],
    [[], step.goal.b],
  ]),
  Con_E1: createRule(true, (step) => [[[], con(step.goal, hole())]]),
  Con_E2: createRule(true, (step) => [[[], con(hole(), step.goal)]]),
  Uni_I: createRule("uni", (step) => {
    let g = "c'";
    const names = [
      ...step.assumptions.flatMap(allNames),
      ...allNames(step.goal.a),
    ];
    while (names.includes(g)) g += "'";
    return {
      steps: [[[], replaceQuantWith(step.goal.a, cnst(g))]],
      intros: cnst(g),
    };
  }),
  Uni_E: createRule<string>(
    (term) => allNames(term).length > 0,
    (step, s) => {
      const goal = preOrderMap(
        step.goal,
        (t) =>
          t.type == "fun" && t.name == s
            ? hole({ ctx: "uni", limit: [quant(0), cnst(s)] })
            : t,
        {}
      );
      return {
        steps: [[[], uni(goal)]],
        intros: cnst(s),
      };
    },
    (step) => unique(allNames(step.goal)).map((n) => [n, n])
  ),
  Exi_I: createRule("exi", (step) => {
    const h = hole({ ctx: "exi" });
    return { steps: [[[], replaceQuantWith(step.goal.a, h)]], intros: h };
  }),
  Exi_E: createRule(true, (step) => {
    const h = hole();
    const w = wrapper(h);
    return [
      [[], exi(h)],
      [[w], step.goal],
    ];
  }),
};
export const applicableSteps = (step: Step) =>
  Object.entries(applyRule)
    .map(([rule, r]) => [rule as Rule, r] as const)
    .filter(([_, r]) => r.canApply(step.goal))
    .map(([rule, r]) =>
      r.options
        ? {
            rule,
            options: r
              .options(step)
              .map(
                ([txt, opt]) =>
                  [txt, () => r.apply(step, opt as never)] as const
              ),
          }
        : {
            rule,
            apply: () => r.apply(step, void 0 as never),
          }
    );

const replaceQuantWith = (term: Term, g: Term): Term =>
  preOrderMap(
    term,
    (t, depth) => {
      if (t.type == "quant" && t.depth == depth) return g;
      else if (t.type == "uni" || t.type == "exi") return [t, depth + 1];
      else return t;
    },
    1
  );

const preOrderMap = <T>(
  term: Term,
  f: (t: Term, ctx: T) => Term | [Term, T],
  ctx: T
): Term => {
  const res = f(term, ctx);
  if (Array.isArray(res)) {
    term = res[0];
    ctx = res[1];
  } else {
    term = res;
  }
  switch (term.type) {
    case "hole":
      return term;
    case "wrapper":
      return term;
    case "falsity":
      return term;
    case "fun":
      return fun(
        term.name,
        term.args.map((t) => preOrderMap(t, f, ctx))
      );
    case "imp":
      return imp(preOrderMap(term.a, f, ctx), preOrderMap(term.b, f, ctx));
    case "con":
      return con(preOrderMap(term.a, f, ctx), preOrderMap(term.b, f, ctx));
    case "dis":
      return dis(preOrderMap(term.a, f, ctx), preOrderMap(term.b, f, ctx));
    case "exi":
      return exi(preOrderMap(term.a, f, ctx));
    case "uni":
      return uni(preOrderMap(term.a, f, ctx));
    case "quant":
      return term;
  }
};
type AuxTerms<T> = {
  [N in keyof Terms]: {
    [K in keyof Terms[N]]: Terms[N][K] extends Term
      ? T
      : Terms[N][K] extends Term[]
      ? T[]
      : Terms[N][K];
  };
};
type AuxTerm<T> = {
  [K in keyof AuxTerms<T>]: { type: K } & AuxTerms<T>[K];
}[keyof AuxTerms<T>];
const foldTerm = <T>(term: Term, f: (t: AuxTerm<T>) => T): T => {
  switch (term.type) {
    case "hole":
      return f(term);
    case "wrapper":
      return f({ type: "wrapper", over: foldTerm(term.over, f) });
    case "falsity":
      return f(term);
    case "fun":
      return f({
        type: "fun",
        name: term.name,
        args: term.args.map((t) => foldTerm(t, f)),
      });
    case "imp":
      return f({ type: "imp", a: foldTerm(term.a, f), b: foldTerm(term.b, f) });
    case "con":
      return f({ type: "con", a: foldTerm(term.a, f), b: foldTerm(term.b, f) });
    case "dis":
      return f({ type: "dis", a: foldTerm(term.a, f), b: foldTerm(term.b, f) });
    case "exi":
      return f({ type: "exi", a: foldTerm(term.a, f) });
    case "uni":
      return f({ type: "uni", a: foldTerm(term.a, f) });
    case "quant":
      return f(term);
  }
};

export type HoleId = string;

type Terms = {
  hole: { id: HoleId; limit?: Term[]; ctx?: "uni" | "exi" };
  wrapper: { over: Term };
  falsity: {};
  imp: { a: Term; b: Term };
  fun: { name: string; args: Term[] };
  con: { a: Term; b: Term };
  dis: { a: Term; b: Term };
  exi: { a: Term };
  uni: { a: Term };
  quant: { depth: number };
};
export type Term = { [K in keyof Terms]: { type: K } & Terms[K] }[keyof Terms];

export type Step = {
  rule: null | Rule;
  preview?: boolean;
  depth?: number;
  intros?: Term;
  assumptions: Term[];
  goal: Term;
};

let holeSeq = Date.now();
export const hole = ({
  id = (++holeSeq).toString(),
  limit,
  ctx,
}: Partial<Terms["hole"]> = {}): Term => ({
  type: "hole",
  limit,
  id,
  ctx,
});
const wrapper = (over: Term): Term => ({ type: "wrapper", over });
export const falsity = (): Term => ({ type: "falsity" });
export const imp = (a: Term, b: Term): Term => ({ type: "imp", a, b });
export const fun = (name: string, args: Term[]): Term => ({
  type: "fun",
  name,
  args,
});
export const cnst = (name: string): Term => ({ type: "fun", name, args: [] });
export const con = (a: Term, b: Term): Term => ({ type: "con", a, b });
export const dis = (a: Term, b: Term): Term => ({ type: "dis", a, b });
export const exi = (a: Term): Term => ({ type: "exi", a });
export const uni = (a: Term): Term => ({ type: "uni", a });
export const quant = (depth: number): Term => ({ type: "quant", depth });

const bumpQuant = (term: Term): Term => {
  if (term.type == "quant") return { type: "quant", depth: term.depth + 1 };
  else return term;
};
export const fillHole = (
  opts: { id: HoleId; allNames: string[]; term: Term },
  src: Term
): Term =>
  fns<Term>({
    hole: (t) => (t.id == opts.id ? opts.term : t),
    wrapper: (t) => {
      let g = "c'";
      while (opts.allNames.includes(g)) g += "'";
      const term = preOrderMap(
        opts.term,
        (t, depth) =>
          t.type == "exi" || t.type == "uni"
            ? [t, depth + 1]
            : t.type == "quant" && t.depth == depth
            ? cnst(g)
            : t,
        0
      );
      // NOTE: Any quant not the outer most must be bumped to account of the
      // extra quantifier on the goal term
      const t2: Term =
        term.type == "quant" && term.depth < 0
          ? { type: "quant", depth: term.depth + 1 }
          : term;
      const w = fillHole({ ...opts, term: t2 }, t.over);
      if (containsHole(w)) {
        return wrapper(w);
      } else {
        return w;
      }
    },
    falsity: (t) => t,
    imp: (t) => imp(fillHole(opts, t.a), fillHole(opts, t.b)),
    fun: (t) =>
      fun(
        t.name,
        t.args.map((a) => fillHole(opts, a))
      ),
    con: (t) => con(fillHole(opts, t.a), fillHole(opts, t.b)),
    dis: (t) => dis(fillHole(opts, t.a), fillHole(opts, t.b)),
    exi: (t) => exi(fillHole({ ...opts, term: bumpQuant(opts.term) }, t.a)),
    uni: (t) => uni(fillHole({ ...opts, term: bumpQuant(opts.term) }, t.a)),
    quant: (t) => t,
  })(src);
export const containsHole = (src: Term): boolean =>
  foldTerm<boolean>(
    src,
    fns({
      hole: () => true,
      wrapper: (t) => t.over,
      falsity: () => false,
      fun: (t) => t.args.includes(true),
      imp: (t) => t.a || t.b,
      con: (t) => t.a || t.b,
      dis: (t) => t.a || t.b,
      exi: (t) => t.a,
      uni: (t) => t.a,
      quant: () => false,
    })
  );
export const allNames = (src: Term): string[] =>
  foldTerm(
    src,
    fns<string[], string[]>({
      hole: () => [],
      wrapper: (t) => t.over,
      falsity: () => [],
      imp: (t) => [...t.a, ...t.b],
      con: (t) => [...t.a, ...t.b],
      dis: (t) => [...t.a, ...t.b],
      fun: (t) => (t.args.length == 0 ? [t.name] : t.args.flat()),
      exi: (t) => t.a,
      uni: (t) => t.a,
      quant: () => [],
    })
  );

const parenIf = (paren: boolean | undefined, s: string) =>
  paren ? `(${s})` : s;

const fns =
  <T, I = Term>(fns: {
    [K in keyof Terms]: (t: AuxTerms<I>[K] & { type: K }) => T;
  }) =>
  (t: AuxTerm<I>) =>
    fns[t.type](t as any);

const precedence = (term: Term, opts: { braceStyle?: BraceStyle }) =>
  fns<[number, number]>({
    hole: () => [0, 0],
    wrapper: () => [0, 0],
    falsity: () => [0, 0],
    imp: () => [7, 8],
    fun: (t) =>
      opts.braceStyle != "ml" ? [0, 1] : t.args.length > 0 ? [1, 1] : [0, 0],
    con: () => [3, 4],
    dis: () => [5, 6],
    exi: () => [2, 2.5],
    uni: () => [2, 2.5],
    quant: () => [0, 0],
  })(term);

export type BraceStyle = "math" | "ml";
export const termToTex = (
  term: Term,
  opts: {
    depth?: number;
    prec?: number;
    braceStyle?: BraceStyle;
  } = {}
): string => {
  const parentPrec = opts.prec ?? 100;
  const prec = precedence(term, { braceStyle: opts.braceStyle });
  const p = Math.min(...prec);
  opts = { ...opts, prec: prec[1] };
  const lopts = { ...opts, prec: prec[0] };
  const ropts = { ...opts, prec: prec[1] };

  const txt = fns({
    hole: (t) =>
      `\\htmlId{hole-${t.id}}{\\htmlStyle{color: var(--hole-${t.id}, #b91c1c);}{\\square}}`,
    wrapper: (t) => `\\{ ${termToTex(t.over, opts)} \\}`,
    falsity: () => "\\bot",
    imp: (t) =>
      `${termToTex(t.a, lopts)} \\rightarrow ${termToTex(t.b, ropts)}`,
    fun: (t) =>
      t.args.length == 0
        ? t.name
        : opts.braceStyle == "ml"
        ? `${t.name} \\; ${t.args.map((a) => termToTex(a, opts)).join("\\;")}`
        : `${t.name}(${t.args
            .map((a) => termToTex(a, { ...opts }))
            .join(", ")})`,
    con: (t) => `${termToTex(t.a, lopts)} \\land ${termToTex(t.b, ropts)}`,
    dis: (t) => `${termToTex(t.a, lopts)} \\lor ${termToTex(t.b, ropts)}`,
    exi: (t) =>
      `\\exists ${qualiNames[opts.depth ?? 0]}. \\; ${termToTex(t.a, {
        ...opts,
        depth: (opts.depth ?? 0) + 1,
      })}`,
    uni: (t) =>
      `\\forall ${qualiNames[opts.depth ?? 0]}. \\; ${termToTex(t.a, {
        ...opts,
        depth: (opts.depth ?? 0) + 1,
      })}`,
    quant: (t) => qualiNames[(opts.depth ?? 0) - t.depth],
    // quant: (t) => `x${t.depth}`,
  })(term);

  return parenIf(p >= parentPrec, txt);
};

const qualiNames = ["x", "y", "z", "u", "v"];

type NestedStep = Step & { children: NestedStep[] };

const nestSteps = (steps: Step[]) => {
  const stack: NestedStep[] = [];
  for (const step of steps) {
    const c = { ...step, children: [] };
    stack[step.depth ?? 0] = c;
    if (step.depth && step.depth > 0) stack[step.depth - 1].children.push(c);
  }
  return stack[0];
};
export const encodeSteps = (steps: Step[]) => encodeStep(nestSteps(steps));
const encodeStep = (step: NestedStep): string => {
  const rule = step.rule?.replaceAll("_", "") || "OK";
  const prevNames = [
    ...step.assumptions.flatMap(allNames),
    ...allNames(step.goal),
  ];
  const intros =
    step.rule == "Uni_I" && step.children[0]
      ? `{Fun{${allNames(step.children[0].goal)
          .find((n) => !prevNames.includes(n))
          ?.replaceAll("'", "*")}}{},1}`
      : "";
  return `${rule}{${encodeTerm(step.goal)}}[${step.assumptions
    .map((a) => encodeTerm(a))
    .join(",")}]${
    step.children.length > 0
      ? `:${intros}${step.children.map((c) => `{${encodeStep(c)}}`).join("")}`
      : ""
  }`;
};
const encodeTerm = (term: Term, inPre = false): string =>
  fns({
    hole: () => ".",
    wrapper: (t) => encodeTerm(t.over, inPre),
    falsity: () => "Falsity",
    imp: (t) => `Imp{${encodeTerm(t.a)}}{${encodeTerm(t.b)}}`,
    fun: (t) => {
      const ann = inPre ? "Fun" : "Pre";
      const name = t.name.replaceAll("'", "*");
      if (t.args.length == 0) return `${ann}{${name}}{}`;
      else
        return `${ann}{${name}}{[${t.args
          .map((a) => encodeTerm(a, true))
          .join(",")}]}`;
    },
    con: (t) => `Con{${encodeTerm(t.a)}}{${encodeTerm(t.b)}}`,
    dis: (t) => `Dis{${encodeTerm(t.a)}}{${encodeTerm(t.b)}}`,
    exi: (t) => `Exi{${encodeTerm(t.a)}}`,
    uni: (t) => `Uni{${encodeTerm(t.a)}}`,
    quant: (t) => `Var{${t.depth - 1}}`,
  })(term);

export const isabellaSteps = (steps: Step[]) =>
  [
    `theorem "semantics e f g (${isabeleTerm(steps[0].goal)})"`,
    "proof (rule soundness)",
    ...isabellaStep(nestSteps(steps), 1).map((s) => "  " + s),
    "qed",
  ]
    .join("\n")
    .replaceAll("(Falsity)", "Falsity");
const isabellaStep = (
  step: NestedStep,
  depth: number,
  prefix: "show" | "have" = "show"
): string[] => {
  const prop = (goal: Term, assumptions: Term[]) =>
    `OK (${isabeleTerm(goal)}) [${assumptions
      .map((a) => isabeleTerm(a))
      .join(", ")}]`;

  const pre = (p: "show" | "have" = prefix) =>
    `${p} "${prop(step.goal, step.assumptions)}"`;

  const sp = (s: string) => "  ".repeat(depth) + s;

  if (step.rule) {
    switch (step.rule) {
      case "Boole":
      case "Imp_I":
      case "Con_I":
      case "Dis_I1":
      case "Dis_I2":
      case "Imp_E":
      case "Dis_E":
      case "Con_E1":
      case "Con_E2":
        return [
          pre(),
          `proof (rule ${step.rule})`,
          ...intersperse(
            ["next"],
            step.children.map((s) => isabellaStep(s, depth).map(sp))
          ).flat(),
          `qed`,
        ];
      case "Uni_E":
        return [
          ...isabellaStep(step.children[0], depth, "have"),
          `then have "OK (sub 0 (${isabeleTerm(
            step.intros ?? cnst("?"),
            true
          )}) (${
            "a" in step.children[0].goal
              ? isabeleTerm(step.children[0].goal.a)
              : ""
          })) [${step.assumptions.map((a) => isabeleTerm(a)).join(", ")}]"`,
          `  by (rule ${step.rule})`,
          // TODO: The prefix here is questionable
          `then ${prefix} "${prop(step.goal, step.assumptions)}"`,
          `  by simp`,
        ];
      case "Exi_E":
        // TODO
        return ["TODO: Exi_E"];
      case "Exi_I":
      case "Uni_I":
        return [
          pre(),
          `proof (rule ${step.rule})`,
          ...isabellaStep(step.children[0], depth, "have").map(sp),
          `  then show "OK (sub 0 (${isabeleTerm(step.intros!, true)}) (${
            "a" in step.goal ? isabeleTerm(step.goal.a) : ""
          })) [${step.assumptions.map((a) => isabeleTerm(a)).join(", ")}]"`,
          `    by simp`,
          `qed${step.rule == "Uni_I" ? " simp" : ""}`,
        ];
    }
  } else {
    return [pre(), `  by (rule Assume) simp`];
  }
};
const isabeleTerm = (term: Term, inPre = false): string =>
  fns<string>({
    hole: () => "?",
    wrapper: (t) => isabeleTerm(t.over, inPre),
    falsity: () => "Falsity",
    imp: (t) => `Imp (${isabeleTerm(t.a)}) (${isabeleTerm(t.b)})`,
    fun: (t) => {
      const ann = inPre ? "Fun" : "Pre";
      const name = t.name.replaceAll("'", "*");
      return `${ann} ''${name}'' [${t.args
        .map((a) => isabeleTerm(a, true))
        .join(", ")}]`;
    },
    con: (t) => `Con (${isabeleTerm(t.a)}) (${isabeleTerm(t.b)})`,
    dis: (t) => `Dis (${isabeleTerm(t.a)}) (${isabeleTerm(t.b)})`,
    exi: (t) => `Exi (${isabeleTerm(t.a)})`,
    uni: (t) => `Uni (${isabeleTerm(t.a)})`,
    quant: (t) => `Var ${t.depth - 1}`,
  })(term);

type Options = [() => Term, string];
export const optionsForHole = (
  step: Step,
  id: HoleId,
  braceStyle: BraceStyle
): readonly Options[] => {
  type HoleCtx = {
    hole?: Terms["hole"];
    inWrapper?: boolean;
    inPre?: boolean;
    quants?: ("uni" | "exi")[];
  };
  const merge = (a: HoleCtx, b: HoleCtx): HoleCtx => {
    if (a.hole && b.hole) {
      return {
        hole: a.hole || b.hole,
        inWrapper: a.inWrapper || b.inWrapper,
        inPre: a.inPre || b.inPre,
        // TODO: This is a bit strage?
        quants: a.quants || b.quants,
      };
    }
    return a.hole ? a : b;
  };

  const ctx = foldTerm<HoleCtx>(
    step.goal,
    fns<HoleCtx, HoleCtx>({
      hole: (t) => {
        if (t.id == id) return { hole: t };
        return {};
      },
      wrapper: (t) => ({ ...t.over, inWrapper: true }),
      falsity: () => ({}),
      fun: (t) => ({ ...t.args.reduce(merge, {}), inPre: true }),
      imp: (t) => merge(t.a, t.b),
      con: (t) => merge(t.a, t.b),
      dis: (t) => merge(t.a, t.b),
      exi: (t) => ({ ...t.a, quants: ["exi", ...(t.a.quants ?? [])] }),
      uni: (t) => ({ ...t.a, quants: ["uni", ...(t.a.quants ?? [])] }),
      quant: () => ({}),
    })
  );

  if (!ctx.hole) return [];
  const hoveredHole = ctx.hole;

  if (hoveredHole.limit)
    return hoveredHole.limit.map<Options>((t) => [
      () => t,
      termToTex(t, { braceStyle }),
    ]);

  const f = (a: string, n: number) =>
    braceStyle == "ml"
      ? `${a} \\; ${range(0, n)
          .map(() => "\\_")
          .join("\\;")}`
      : `${a}(${range(0, n)
          .map(() => "\\_")
          .join(", ")})`;

  const staticOptions: Options[] = [
    [() => cnst("a"), "a"],
    [() => cnst("b"), "b"],
    [() => cnst("c"), "c"],
    [() => cnst("f"), "f"],
    [() => cnst("A"), "A"],
    [() => cnst("B"), "B"],
    [() => cnst("C"), "C"],
    [() => cnst("D"), "D"],
    [() => fun("A", [hole()]), f("A", 1)],
    [() => fun("B", [hole()]), f("B", 1)],
    [() => fun("C", [hole()]), f("C", 1)],
    [() => fun("f", [hole()]), f("f", 1)],
    [() => fun("A", [hole(), hole()]), f("A", 2)],
    [() => fun("B", [hole(), hole()]), f("B", 2)],
    [() => fun("C", [hole(), hole()]), f("C", 2)],
    [() => fun("f", [hole(), hole()]), f("f", 2)],
  ];
  const terms: Options[] = ctx.inPre
    ? []
    : [
        [() => falsity(), "\\bot"],
        [() => imp(hole(), hole()), "\\rightarrow"],
        [() => con(hole(), hole()), "\\land"],
        [() => dis(hole(), hole()), "\\lor"],
        [() => exi(hole()), "\\exists"],
        [() => uni(hole()), "\\forall"],
      ];
  const qualifiers = qualiNames
    .slice(0, ctx.quants?.length ?? 0)
    .map<Options>((n, i) => [() => quant(-i), n])
    .filter((_, i) =>
      hoveredHole.ctx == "exi" ? ctx.quants?.[i] != "uni" : true
    );

  const constants = [
    ...step.assumptions.flatMap(allNames),
    ...allNames(step.goal),
  ].map<Options>((n) => [() => cnst(n), n]);

  const unify = (a: Term, b: Term): false | [HoleId, Term][] => {
    if (a.type == "hole") return [[a.id, b]];
    if (b.type == "hole") return [[b.id, a]];

    if (a.type != b.type) return false;

    if (a.type == "falsity") return [];
    else if ("a" in a && "a" in b && "b" in a && "b" in b) {
      const ua = unify(a.a, b.a);
      const ub = unify(a.b, b.b);
      if (!ua || !ub) return false;
      return [...ua, ...ub];
    } else if (a.type == "fun" && b.type == "fun") {
      if (a.name != b.name) return false;
      const args = a.args.map((x, i) => unify(x, b.args[i]));
      if (args.includes(false)) return false;
      return args.filter(isTruthy).flat();
    } else {
      return false;
    }
  };

  const unifications = step.assumptions
    .map((a) => unify(a, step.goal))
    .filter(isTruthy)
    .flat()
    .filter(([n]) => n == id)
    .map<Options>(([, t]) => [() => t, termToTex(t, { braceStyle })]);

  const options: Options[] = [
    ...staticOptions,
    ...terms,
    ...qualifiers,
    ...constants,
    ...unifications,
  ];

  // NOTE: Deduplicate
  return options.filter(
    ([_, n], i, rest) => i == rest.findIndex(([_, m]) => n == m)
  );
};

// TODO: When a proof for this is found, work on Export Isabelle for Exi_E
// https://philosophy.stackexchange.com/questions/65203/help-with-an-existential-natural-deduction-proof
