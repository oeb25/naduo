import React, { useCallback, useRef, useState } from "react";
import { Katex } from "./Katex";
import { isTruthy, range, unique } from "./utils";
import { useFloating, shift, Placement } from "@floating-ui/react-dom";
import * as Hero from "@heroicons/react/outline";
import equal from "fast-deep-equal";
import { useLocalStorage } from "./hooks";

export const App = () => {
  return (
    <div className="container flex h-screen py-10 mx-auto text-gray-50">
      <ProofSection />
    </div>
  );
};

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
type Rule = typeof RULES[number];
function createRule<
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
  ) => Omit<[Term[], Term], "rule">[],
  options?: (step: Step) => [string, Args][]
): {
  canApply: (term: Term) => boolean;
  apply: (step: Step, args: Args) => Step[];
  options?: (step: Step) => [string, Args][];
} {
  return {
    canApply:
      typeof canApply == "string"
        ? (t) => t.type == canApply
        : typeof canApply == "function"
        ? canApply
        : (_) => true,
    apply: (step, args) =>
      apply(step as any, args).map(([assumptions, goal]) => ({
        rule: null,
        assumptions: [...assumptions, ...step.assumptions],
        goal,
      })),
    options,
  };
}
const applyRule = {
  Boole: createRule(true, (step) => [[[imp(step.goal, falsify())], falsify()]]),
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
    return [[[], replaceQuantWith(step.goal.a, cnst(g))]];
  }),
  Uni_E: createRule<string>(
    (term) => allNames(term).length > 0,
    (step, s) => [
      [
        [],
        uni(
          preOrderMap(
            step.goal,
            (t) =>
              t.type == "fun" && t.name == s
                ? hole({
                    ctx: "uni",
                    limit: [quant(0), cnst(s)],
                  })
                : t,
            {}
          )
        ),
      ],
    ],
    (step) => unique(allNames(step.goal)).map((n) => [n, n])
  ),
  Exi_I: createRule("exi", (step) => [
    [[], replaceQuantWith(step.goal.a, hole({ ctx: "exi" }))],
  ]),
  Exi_E: createRule(true, (step) => {
    const h = hole();
    const w = wrapper(h);
    return [
      [[], exi(h)],
      [[w], step.goal],
    ];
  }),
};
const applicableSteps = (step: Step) =>
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

function preOrderMap<T>(
  term: Term,
  f: (t: Term, ctx: T) => Term | [Term, T],
  ctx: T
): Term {
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
    case "falsify":
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
}
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
function foldTerm<T>(term: Term, f: (t: AuxTerm<T>) => T): T {
  switch (term.type) {
    case "hole":
      return f(term);
    case "wrapper":
      return f({ type: "wrapper", over: foldTerm(term.over, f) });
    case "falsify":
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
}

type HoleId = string;

type Terms = {
  hole: { id: HoleId; limit?: Term[]; ctx?: "uni" | "exi" };
  wrapper: { over: Term };
  falsify: {};
  imp: { a: Term; b: Term };
  fun: { name: string; args: Term[] };
  con: { a: Term; b: Term };
  dis: { a: Term; b: Term };
  exi: { a: Term };
  uni: { a: Term };
  quant: { depth: number };
};
type Term = { [K in keyof Terms]: { type: K } & Terms[K] }[keyof Terms];

type Step = {
  rule: null | Rule;
  preview?: boolean;
  depth?: number;
  assumptions: Term[];
  goal: Term;
};

let holeSeq = Date.now();
const hole = ({
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
const falsify = (): Term => ({ type: "falsify" });
const imp = (a: Term, b: Term): Term => ({ type: "imp", a, b });
const fun = (name: string, args: Term[]): Term => ({ type: "fun", name, args });
const cnst = (name: string): Term => ({ type: "fun", name, args: [] });
const con = (a: Term, b: Term): Term => ({ type: "con", a, b });
const dis = (a: Term, b: Term): Term => ({ type: "dis", a, b });
const exi = (a: Term): Term => ({ type: "exi", a });
const uni = (a: Term): Term => ({ type: "uni", a });
const quant = (depth: number): Term => ({ type: "quant", depth });

const h0 = hole();

const ProofSection = () => {
  const [stack, setStack] = useLocalStorage<Step[][]>("naduo-steps", [
    [{ rule: null, assumptions: [], goal: h0 }],
  ]);
  const [cursor, setCursor] = useState(stack.length - 1);
  const back = useCallback(
    () => setCursor((c) => Math.max(c - 1, 0)),
    [setCursor]
  );
  const forward = useCallback(
    () => setCursor((c) => Math.min(c + 1, stack.length - 1)),
    [setCursor, stack.length]
  );
  const controls = useRef({ back, forward });
  controls.current = { back, forward };
  const steps = stack[cursor];
  const setSteps = (f: (steps: Step[]) => Step[]) => {
    setStack((stack) => [...stack.slice(0, cursor + 1), f(stack[cursor])]);
    setCursor(cursor + 1);
  };
  const [preview, setPreview] = useState<typeof steps | void>(void 0);

  React.useEffect(() => {
    const listener = (e: KeyboardEvent) => {
      if (e.metaKey || e.ctrlKey) {
        if (e.key == "z")
          if (e.shiftKey) controls.current.forward();
          else controls.current.back();
      }
      if (e.key == "ArrowLeft") controls.current.back();
      if (e.key == "ArrowRight") controls.current.forward();
    };

    window.addEventListener("keydown", listener);
    return () => window.removeEventListener("keydown", listener);
  }, [back, forward]);

  return (
    <div
      className="relative grid w-full h-full"
      style={{ gridTemplateRows: "1fr auto" }}
    >
      <div className="overflow-y-auto">
        {(preview ?? steps).map((step, i) => (
          <StepView
            key={i}
            step={step}
            setHole={(id, term) => {
              const an = [
                ...step.assumptions.flatMap((s) => allNames(s)),
                ...allNames(step.goal),
              ];
              const opts = { id, allNames: an, term };
              setSteps((steps) =>
                steps.map((step) => ({
                  ...step,
                  assumptions: step.assumptions.map((t) => fillHole(opts, t)),
                  goal: fillHole(opts, step.goal),
                }))
              );
            }}
            onHoverRule={([rule, newSteps]) => {
              if (rule) {
                setPreview(() => [
                  ...steps.slice(0, i),
                  steps[i],
                  ...newSteps.map((s) => ({
                    ...s,
                    preview: true,
                    depth: (steps[i].depth ?? 0) + 1,
                  })),
                  ...steps.slice(i + 1),
                ]);
              } else {
                setPreview(void 0);
              }
            }}
            chooseRule={([rule, steps]) => {
              setPreview(void 0);
              setSteps((ss) => [
                ...ss.slice(0, i),
                { ...ss[i], rule },
                ...steps.map((s) => ({ ...s, depth: (ss[i].depth ?? 0) + 1 })),
                ...ss.slice(i + 1),
              ]);
            }}
          />
        ))}
      </div>
      <div className="flex flex-col items-center justify-center">
        <input
          className="w-full max-w-lg"
          type="range"
          min={0}
          max={stack.length - 1}
          step={1}
          value={cursor}
          onChange={(e) => setCursor(parseInt(e.target.value))}
        />
        <div className="font-mono text-gray-500">
          {cursor + 1} / {stack.length}
        </div>
        <div className="flex text-gray-400">
          <button className="focus hover:text-gray-100" onClick={back}>
            <Hero.RewindIcon className="w-8 h-8 transition" />
          </button>
          <button className="focus hover:text-gray-100" onClick={forward}>
            <Hero.FastForwardIcon className="w-8 h-8 transition" />
          </button>
        </div>
      </div>
      <div className="flex flex-col items-center justify-center">
        <button
          className="flex items-center space-x-1 text-gray-400 transition hover:text-gray-100"
          onClick={() =>
            window.navigator.clipboard.writeText(
              // encodeSteps(steps)
              stack.map(encodeSteps).reverse().join("\n")
            )
          }
        >
          <span>Export</span> <Hero.SaveIcon className="w-5 h-5" />
        </button>
      </div>
    </div>
  );
};

const bumpQuant = (term: Term): Term => {
  if (term.type == "quant") return { type: "quant", depth: term.depth + 1 };
  else return term;
};
const fillHole = (
  opts: { id: HoleId; allNames: string[]; term: Term },
  src: Term
): Term =>
  fns<Term>({
    hole: (t) => (t.id == opts.id ? opts.term : t),
    wrapper: (t) => {
      // TODO
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
      const w = fillHole({ ...opts, term }, t.over);
      if (containsHole(w)) {
        return wrapper(w);
      } else {
        return w;
      }
    },
    falsify: (t) => t,
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
const containsHole = (src: Term): boolean =>
  foldTerm<boolean>(
    src,
    fns({
      hole: () => true,
      wrapper: (t) => t.over,
      falsify: () => false,
      fun: (t) => t.args.includes(true),
      imp: (t) => t.a || t.b,
      con: (t) => t.a || t.b,
      dis: (t) => t.a || t.b,
      exi: (t) => t.a,
      uni: (t) => t.a,
      quant: () => false,
    })
  );
const allNames = (src: Term): string[] =>
  foldTerm(
    src,
    fns<string[], string[]>({
      hole: () => [],
      wrapper: (t) => t.over,
      falsify: () => [],
      imp: (t) => [...t.a, ...t.b],
      con: (t) => [...t.a, ...t.b],
      dis: (t) => [...t.a, ...t.b],
      fun: (t) => (t.args.length == 0 ? [t.name] : t.args.flat()),
      exi: (t) => t.a,
      uni: (t) => t.a,
      quant: () => [],
    })
  );

const StepView = ({
  step,
  setHole,
  onHoverRule,
  chooseRule,
}: {
  step: Step;
  setHole: (id: HoleId, term: Term) => void;
  onHoverRule: (rule: [Rule | void, Step[]]) => void;
  chooseRule: (rule: [Rule, Step[]]) => void;
}) => {
  const [hovered, setHovered] = useState<{ id: HoleId; el: HTMLElement }>();
  const rect = hovered?.el.getBoundingClientRect();

  const options = hovered?.id && optionsForHole(step, hovered.id);

  return (
    <div
      className={`flex relative ${
        step.preview ? "opacity-50 pointer-events-none select-none" : ""
      }`}
    >
      <div className="text-center w-36">
        {step.assumptions.find((a) => equal(a, step.goal)) ? (
          <Katex src={`\\textbf{Assumption}`} />
        ) : step.rule ? (
          <Katex
            src={`\\textbf{${step.rule
              .replaceAll("_", " ")
              .replaceAll(/(\d)/g, "}_{$1")}}`}
          />
        ) : containsHole(step.goal) ? (
          "..."
        ) : (
          <Menu
            text="??"
            placement="bottom"
            className="w-full font-bold text-red-800"
          >
            {() => (
              <>
                {applicableSteps(step).map((r) => {
                  const label = (
                    <Katex
                      src={`\\textbf{${r.rule
                        .replaceAll("_", " ")
                        .replaceAll(/(\d)/g, "}_{$1")}}`}
                    />
                  );
                  return r.options ? (
                    <Menu
                      key={r.rule}
                      text={label}
                      placement="right-start"
                      className="p-2 border border-gray-600 hover:bg-gray-800 first:rounded-t last:rounded-b text-gray-50"
                    >
                      {() => (
                        <>
                          {r.options.map(([n, apply]) => (
                            <button
                              key={n}
                              className="p-2 border border-gray-600 hover:bg-gray-800 first:rounded-t last:rounded-b"
                              onClick={() => chooseRule([r.rule, apply()])}
                              onMouseEnter={() =>
                                onHoverRule([r.rule, apply()])
                              }
                              onMouseLeave={() => onHoverRule([void 0, []])}
                            >
                              <Katex src={n} />
                            </button>
                          ))}
                        </>
                      )}
                    </Menu>
                  ) : (
                    <button
                      key={r.rule}
                      className="p-2 border border-gray-600 hover:bg-gray-800 first:rounded-t last:rounded-b text-gray-50"
                      onClick={() => chooseRule([r.rule, r.apply()])}
                      onMouseEnter={() => onHoverRule([r.rule, r.apply()])}
                      onMouseLeave={() => onHoverRule([void 0, []])}
                    >
                      {label}
                    </button>
                  );
                })}
              </>
            )}
          </Menu>
        )}
      </div>
      {hovered && (
        <style
          dangerouslySetInnerHTML={{
            __html: `* { --hole-${hovered.id}: #dc2626; }`,
          }}
        />
      )}
      <div onMouseLeave={() => setHovered(void 0)}>
        {hovered && rect && options ? (
          <div
            className="fixed z-10 -translate-x-1/2"
            style={{
              top: rect.top,
              left: rect.left + rect.width / 2,
            }}
          >
            <div className="grid grid-flow-row-dense grid-cols-4 mt-5 overflow-hidden bg-gray-900 border border-gray-600 rounded shadow w-72">
              {options.map(([f, tex]) => (
                <button
                  key={tex}
                  className="px-1 py-1 border border-gray-600/10 hover:bg-gray-800"
                  onClick={() => {
                    setHole(hovered.id, f());
                    setHovered(void 0);
                  }}
                >
                  <Katex src={tex} />
                </button>
              ))}
            </div>
          </div>
        ) : null}
        <div
          onMouseMove={(e) => {
            let t = e.target as HTMLElement | undefined | null;
            while (t && !t.id?.startsWith("hole-")) t = t.parentElement;
            if (t) {
              if (t != hovered?.el)
                setHovered({ el: t, id: t.id.substring(5) });
            } else {
              setHovered(void 0);
            }
          }}
          style={{
            marginLeft: (step.depth ?? 0) + "em",
          }}
        >
          <Katex
            src={`\\left[${
              step.assumptions.map((t) => termToTex(t, {})).join(", ") || "\\;"
            }\\right] \\;\\;\\; ${termToTex(step.goal, {})}`}
          />
        </div>
      </div>
    </div>
  );
};

const parenIf = (paren: boolean | undefined, s: string) =>
  paren ? `(${s})` : s;

function fns<T, I = Term>(fns: {
  [K in keyof Terms]: (t: AuxTerms<I>[K] & { type: K }) => T;
}) {
  return (t: AuxTerm<I>) => fns[t.type](t as any);
}

const precedence = (term: Term, opts: { mlStyle?: boolean }) =>
  fns<[number, number]>({
    hole: () => [0, 0],
    wrapper: () => [0, 0],
    falsify: () => [0, 0],
    imp: () => [7, 8],
    fun: (t) => (!opts.mlStyle ? [0, 1] : t.args.length > 0 ? [1, 1] : [0, 0]),
    con: () => [3, 4],
    dis: () => [5, 6],
    exi: () => [2, 2],
    uni: () => [2, 2],
    quant: () => [0, 0],
  })(term);

const termToTex = (
  term: Term,
  opts: {
    depth?: number;
    prec?: number;
  } = {}
): string => {
  const mlStyle = false;

  const parentPrec = opts.prec ?? 100;
  const prec = precedence(term, { mlStyle });
  const p = Math.min(...prec);
  opts = { ...opts, prec: prec[1] };
  const lopts = { ...opts, prec: prec[0] };
  const ropts = { ...opts, prec: prec[1] };

  const txt = fns({
    hole: (t) =>
      `\\htmlId{hole-${t.id}}{\\htmlStyle{color: var(--hole-${t.id}, #b91c1c);}{\\square}}`,
    wrapper: (t) => `\\{ ${termToTex(t.over, opts)} \\}`,
    falsify: () => "\\bot",
    imp: (t) =>
      `${termToTex(t.a, lopts)} \\rightarrow ${termToTex(t.b, ropts)}`,
    fun: (t) =>
      t.args.length == 0
        ? t.name
        : mlStyle
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
    // `x${term.depth}`,
  })(term);

  return parenIf(p >= parentPrec, txt);
};

const qualiNames = ["x", "y", "z", "u", "v"];

const Menu = ({
  text,
  className,
  children,
  placement,
}: {
  text: React.ReactNode;
  className?: string;
  children: () => React.ReactElement;
  placement: Placement;
}) => {
  const { x, y, reference, floating, strategy } = useFloating({
    placement,
    middleware: [shift()],
  });

  const [show, setShow] = useState(false);

  return (
    <div
      ref={reference}
      className={className}
      onMouseEnter={() => setShow(true)}
      onMouseLeave={() => setShow(false)}
    >
      {text}
      {show && (
        <div
          ref={floating}
          style={{
            position: strategy,
            top: y ?? "",
            left: x ?? "",
          }}
          className="z-10 flex flex-col bg-gray-900 rounded shadow"
        >
          {children()}
        </div>
      )}
    </div>
  );
};

type NestedStep = Step & { children: NestedStep[] };

const encodeSteps = (steps: Step[]) => {
  const stack: NestedStep[] = [];
  for (const step of steps) {
    const c = { ...step, children: [] };
    stack[step.depth ?? 0] = c;
    if (step.depth && step.depth > 0) stack[step.depth - 1].children.push(c);
  }
  return encodeStep(stack[0]);
};
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
    falsify: () => "Falsity",
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
type Options = [() => Term, string];
function optionsForHole(step: Step, id: HoleId): readonly Options[] {
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
      falsify: () => ({}),
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
    return hoveredHole.limit.map<Options>((t) => [() => t, termToTex(t, {})]);

  const mlStyle = false;
  const f = (a: string, n: number) =>
    mlStyle
      ? `${a} \\; ${range(0, n)
          .map(() => "\\_")
          .join("\\;")}`
      : `${a}(${range(0, n)
          .map(() => "_")
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
        [() => falsify(), "\\bot"],
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

    if (a.type == "falsify") return [];
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
    .map<Options>(([, t]) => [() => t, termToTex(t, {})]);

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
}
