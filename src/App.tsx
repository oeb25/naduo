import React, { useCallback, useRef, useState } from "react";
import { Katex } from "./Katex";
import { isTruthy, unique } from "./utils";
import { useFloating, shift, Placement } from "@floating-ui/react-dom";
import * as Hero from "@heroicons/react/outline";
import equal from "fast-deep-equal";
import { useLocalStorage } from "./hooks";

export const App = () => {
  return (
    <div className="container flex h-screen p-10 mx-auto text-gray-50">
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
function createRule<Args = void>(opts: {
  canApply: (term: Term) => boolean;
  apply: (step: Step, args: Args) => Step[];
}) {
  return opts;
}
const applyRule = {
  Boole: createRule({
    canApply: () => true,
    apply: (step) => [
      {
        rule: null,
        assumptions: [imp(step.goal, falsify()), ...step.assumptions],
        goal: falsify(),
      },
    ],
  }),
  Imp_I: createRule({
    canApply: (term) => term.type == "imp",
    apply: (step) => {
      if (step.goal.type != "imp") throw "nooo";
      return [
        {
          rule: null,
          assumptions: [step.goal.a, ...step.assumptions],
          goal: step.goal.b,
        },
      ];
    },
  }),
  Imp_E: createRule({
    canApply: () => true,
    apply: (step) => {
      const h = hole();
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: imp(h, step.goal),
        },
        {
          rule: null,
          assumptions: step.assumptions,
          goal: h,
        },
      ];
    },
  }),
  Dis_E: createRule({
    canApply: () => true,
    apply: (step) => {
      const a = hole();
      const b = hole();
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: dis(a, b),
        },
        {
          rule: null,
          assumptions: [a, ...step.assumptions],
          goal: step.goal,
        },
        {
          rule: null,
          assumptions: [b, ...step.assumptions],
          goal: step.goal,
        },
      ];
    },
  }),
  Dis_I1: createRule({
    canApply: (term) => term.type == "dis",
    apply: (step) => {
      if (step.goal.type != "dis") throw "nooo";
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: step.goal.a,
        },
      ];
    },
  }),
  Dis_I2: createRule({
    canApply: (term) => term.type == "dis",
    apply: (step) => {
      if (step.goal.type != "dis") throw "nooo";
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: step.goal.b,
        },
      ];
    },
  }),
  Con_I: createRule({
    canApply: (term) => term.type == "con",
    apply: (step) => {
      if (step.goal.type != "con") throw "nooo";
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: step.goal.a,
        },
        {
          rule: null,
          assumptions: step.assumptions,
          goal: step.goal.b,
        },
      ];
    },
  }),
  Con_E1: createRule({
    canApply: () => true,
    apply: (step) => [
      {
        rule: null,
        assumptions: step.assumptions,
        goal: con(step.goal, hole()),
      },
    ],
  }),
  Con_E2: createRule({
    canApply: () => true,
    apply: (step) => [
      {
        rule: null,
        assumptions: step.assumptions,
        goal: con(hole(), step.goal),
      },
    ],
  }),
  Uni_I: createRule({
    canApply: (term) => term.type == "uni",
    apply: (step) => {
      if (step.goal.type != "uni") throw "nooo";
      let g = "c'";
      const names = allNames(step.goal.a);
      while (names.includes(g)) g += "'";
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: replaceQuantWith(step.goal.a, cnst(g)),
        },
      ];
    },
  }),
  Uni_E: createRule<string>({
    canApply: (term) => allNames(term).length > 0,
    apply: (step, s) => {
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: uni(
            preOrderMap(
              step.goal,
              (t) => {
                if (t.type == "fun" && t.name == s)
                  return hole({
                    id: void 0,
                    limit: [quant(0), cnst(s)],
                    ctx: "uni",
                  });
                else return t;
              },
              {}
            )
          ),
        },
      ];
    },
  }),
  Exi_I: createRule({
    canApply: (term) => term.type == "exi",
    apply: (step) => {
      if (step.goal.type != "exi") throw "nooo";
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: replaceQuantWith(step.goal.a, hole({ ctx: "exi" })),
        },
      ];
    },
  }),
  Exi_E: createRule({
    canApply: () => true,
    apply: (step) => {
      const h = hole();
      const w = wrapper(h);
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: exi(h),
        },
        {
          rule: null,
          assumptions: [w, ...step.assumptions],
          goal: step.goal,
        },
      ];
    },
  }),
};
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
const termBuilder: Partial<{
  [K in Exclude<keyof Terms, "hole">]: [() => Term, string];
}> = {
  falsify: [() => falsify(), "\\bot"],
  imp: [() => imp(hole(), hole()), "\\rightarrow"],
  con: [() => con(hole(), hole()), "\\land"],
  dis: [() => dis(hole(), hole()), "\\lor"],
  exi: [() => exi(hole()), "\\exists"],
  uni: [() => uni(hole()), "\\forall"],
};

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
            onHoverRule={(r) => {
              if (r[0]) {
                const x = r as { [K in keyof A]: [K, A[K]] }[keyof A];
                setPreview(() => {
                  const ss = steps;
                  return [
                    ...ss.slice(0, i),
                    ss[i],
                    ...applyRule[x[0]].apply(ss[i], x[1] as never).map((s) => ({
                      ...s,
                      preview: true,
                      depth: (ss[i].depth ?? 0) + 1,
                    })),
                    ...ss.slice(i + 1),
                  ];
                });
              } else {
                setPreview(void 0);
              }
            }}
            chooseRule={(r) => {
              const x = r as { [K in keyof A]: [K, A[K]] }[keyof A];
              setPreview(void 0);
              setSteps((ss) => [
                ...ss.slice(0, i),
                { ...ss[i], rule: x[0] },
                ...applyRule[x[0]]
                  .apply(ss[i], x[1] as never)
                  .map((s) => ({ ...s, depth: (ss[i].depth ?? 0) + 1 })),
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
          {/* <Hero.PlayIcon className="w-8 h-8 transition" /> */}
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
              encodeSteps(steps)
              // stack.map(encodeSteps).reverse().join("\n")
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
): Term => {
  // return preOrderMap(
  //   src,
  //   (t, opts) => {
  //     if (t.type == "hole" && t.id == opts.id) return opts.term;
  //     else if (t.type == "exi" || t.type == "uni")
  //       return [t, { ...opts, term: bumpQuant(opts.term) }];
  //     else return t;
  //   },
  //   opts
  // );

  switch (src.type) {
    case "hole":
      if (src.id == opts.id) return opts.term;
      else return src;
    case "wrapper":
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
      const w = fillHole({ ...opts, term }, src.over);
      if (containsHole(w)) {
        return wrapper(w);
      } else {
        return w;
      }
    case "falsify":
      return src;
    case "imp":
      return imp(fillHole(opts, src.a), fillHole(opts, src.b));
    case "fun":
      return fun(
        src.name,
        src.args.map((a) => fillHole(opts, a))
      );
    case "con":
      return con(fillHole(opts, src.a), fillHole(opts, src.b));
    case "dis":
      return dis(fillHole(opts, src.a), fillHole(opts, src.b));
    case "exi":
      return exi(fillHole({ ...opts, term: bumpQuant(opts.term) }, src.a));
    case "uni":
      return uni(fillHole({ ...opts, term: bumpQuant(opts.term) }, src.a));
    case "quant":
      return src;
  }
};
const containsHole = (src: Term): boolean =>
  foldTerm<boolean>(src, (t) => {
    switch (t.type) {
      case "hole":
        return true;
      case "wrapper":
        return t.over;
      case "falsify":
        return false;
      case "fun":
        return t.args.includes(true);
      case "imp":
      case "con":
      case "dis":
        return t.a || t.b;
      case "exi":
      case "uni":
        return t.a;
      case "quant":
        return false;
    }
  });
const allNames = (src: Term): string[] =>
  foldTerm(src, (t) => {
    switch (t.type) {
      case "hole":
        return [];
      case "wrapper":
        return t.over;
      case "falsify":
        return [];
      case "imp":
      case "con":
      case "dis":
        return [...t.a, ...t.b];
      case "fun":
        if (t.args.length == 0) return [t.name];
        else return t.args.flat();
      case "exi":
      case "uni":
        return t.a;
      case "quant":
        return [];
    }
  });
type A = { [K in Rule]: Parameters<typeof applyRule[K]["apply"]>[1] };

const StepView = ({
  step,
  setHole,
  onHoverRule,
  chooseRule,
}: {
  step: Step;
  setHole: (id: HoleId, term: Term) => void;
  onHoverRule: <R extends keyof A | void>(
    rule: [R, R extends keyof A ? A[R] : void]
  ) => void;
  chooseRule: <R extends keyof A>(rule: [R, A[R]]) => void;
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
                {RULES.filter((r) => applyRule[r].canApply(step.goal)).map(
                  (r) =>
                    r == "Uni_E" ? (
                      <Menu
                        key={r}
                        text={
                          <Katex
                            src={`\\textbf{${r
                              .replaceAll("_", " ")
                              .replaceAll(/(\d)/g, "}_{$1")}}`}
                          />
                        }
                        placement="right-start"
                        className="p-2 border border-gray-600 hover:bg-gray-800 first:rounded-t last:rounded-b text-gray-50"
                      >
                        {() => (
                          <>
                            {unique(allNames(step.goal)).map((n) => (
                              <button
                                key={n}
                                className="p-2 border border-gray-600 hover:bg-gray-800 first:rounded-t last:rounded-b"
                                onClick={() => chooseRule([r, n])}
                                onMouseEnter={() => onHoverRule([r, n])}
                                onMouseLeave={() =>
                                  onHoverRule([void 0, void 0])
                                }
                              >
                                <Katex src={n} />
                              </button>
                            ))}
                          </>
                        )}
                      </Menu>
                    ) : (
                      <button
                        key={r}
                        className="p-2 border border-gray-600 hover:bg-gray-800 first:rounded-t last:rounded-b text-gray-50"
                        onClick={() => chooseRule([r, void 0])}
                        onMouseEnter={() => onHoverRule([r, void 0])}
                        onMouseLeave={() => onHoverRule([void 0, void 0])}
                      >
                        <Katex
                          src={`\\textbf{${r
                            .replaceAll("_", " ")
                            .replaceAll(/(\d)/g, "}_{$1")}}`}
                        />
                      </button>
                    )
                )}
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
              step.assumptions.map((t) => termToTex(t, 0)).join(", ") || "\\;"
            }\\right] \\;\\;\\; ${termToTex(step.goal, 0)}`}
          />
        </div>
      </div>
    </div>
  );
};

const termToTex = (term: Term, depth: number): string => {
  switch (term.type) {
    case "hole":
      return `\\htmlId{hole-${term.id}}{\\htmlStyle{color: var(--hole-${term.id}, #b91c1c);}{\\square}}`;
    case "wrapper":
      return `\\{ ${termToTex(term.over, depth)} \\}`;
    case "falsify":
      return "\\bot";
    case "imp":
      return `(${termToTex(term.a, depth)} \\rightarrow ${termToTex(
        term.b,
        depth
      )})`;
    case "fun":
      if (term.args.length == 0) return term.name;
      else
        return `${term.name}(${term.args
          .map((a) => termToTex(a, depth))
          .join(", ")})`;
    case "con":
      return `(${termToTex(term.a, depth)} \\land ${termToTex(term.b, depth)})`;
    case "dis":
      return `(${termToTex(term.a, depth)} \\lor ${termToTex(term.b, depth)})`;
    case "exi":
      return `\\exists ${qualiNames[depth]}. ${termToTex(term.a, depth + 1)}`;
    case "uni":
      return `\\forall ${qualiNames[depth]}. ${termToTex(term.a, depth + 1)}`;
    case "quant":
      return qualiNames[depth - term.depth];
    // return `x${term.depth}`;
  }
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

const encodeTerm = (term: Term, inPre = false): string => {
  switch (term.type) {
    case "hole":
      return ".";
    case "wrapper":
      return encodeTerm(term.over, inPre);
    case "falsify":
      return "Falsity";
    case "imp":
      return `Imp{${encodeTerm(term.a)}}{${encodeTerm(term.b)}}`;
    case "fun":
      const ann = inPre ? "Fun" : "Pre";
      const name = term.name.replaceAll("'", "*");
      if (term.args.length == 0) return `${ann}{${name}}{}`;
      else
        return `${ann}{${name}}{[${term.args
          .map((a) => encodeTerm(a, true))
          .join(",")}]}`;
    case "con":
      return `Con{${encodeTerm(term.a)}}{${encodeTerm(term.b)}}`;
    case "dis":
      return `Dis{${encodeTerm(term.a)}}{${encodeTerm(term.b)}}`;
    case "exi":
      return `Exi{${encodeTerm(term.a)}}`;
    case "uni":
      return `Uni{${encodeTerm(term.a)}}`;
    case "quant":
      return `Var{${term.depth - 1}}`;
  }
};
function optionsForHole(
  step: Step,
  id: HoleId
): readonly [() => Term, string][] {
  type HoleCtx = {
    hole?: Terms["hole"];
    inWrapper?: boolean;
    inPre?: boolean;
    quants?: ("uni" | "exi")[];
  };
  const wrapWith = (a: HoleCtx, b: HoleCtx): HoleCtx =>
    a.hole || b.hole
      ? {
          hole: a.hole || b.hole,
          inWrapper: a.inWrapper || b.inWrapper,
          inPre: a.inPre || b.inPre,
          quants: [...(b.quants ?? []), ...(a.quants ?? [])],
        }
      : a.hole
      ? a
      : b;

  const ctx = foldTerm<HoleCtx>(step.goal, (t) => {
    switch (t.type) {
      case "hole":
        if (t.id == id) return { hole: t };
        return {};
      case "wrapper":
        return wrapWith(t.over, { inWrapper: true });
      case "falsify":
        return {};
      case "fun":
        return t.args.reduce(wrapWith, { inPre: true });
      case "imp":
      case "con":
      case "dis":
        const a = t.a;
        const b = t.b;
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
      case "exi":
        return wrapWith(t.a, { quants: ["exi"] });
      case "uni":
        return wrapWith(t.a, { quants: ["uni"] });
      case "quant":
        return {};
    }
  });

  if (!ctx.hole) return [];
  const hoveredHole = ctx.hole;

  if (hoveredHole.limit)
    return hoveredHole.limit.map<[() => Term, string]>((t) => [
      () => t,
      termToTex(t, 0),
    ]);

  const staticOptions: [() => Term, string][] = [
    [() => cnst("a"), "a"],
    [() => cnst("b"), "b"],
    [() => cnst("c"), "c"],
    [() => cnst("f"), "f"],
    [() => cnst("A"), "A"],
    [() => cnst("B"), "B"],
    [() => cnst("C"), "C"],
    [() => cnst("D"), "D"],
    [() => fun("A", [hole()]), "A(\\_)"],
    [() => fun("B", [hole()]), "B(\\_)"],
    [() => fun("C", [hole()]), "C(\\_)"],
    [() => fun("f", [hole()]), "f(\\_)"],
    [() => fun("A", [hole(), hole()]), "A(\\_, \\_)"],
    [() => fun("B", [hole(), hole()]), "B(\\_, \\_)"],
    [() => fun("C", [hole(), hole()]), "C(\\_, \\_)"],
    [() => fun("f", [hole(), hole()]), "f(\\_, \\_)"],
  ];
  const terms = ctx.inPre ? [] : Object.values(termBuilder);
  const qualifiers = qualiNames
    .slice(0, ctx.quants?.length ?? 0)
    .map<[() => Term, string]>((n, i) => [() => quant(-i), n])
    .filter((_, i) =>
      hoveredHole.ctx == "exi" ? ctx.quants?.[i] != "uni" : true
    );

  const constants = [
    ...step.assumptions.flatMap(allNames),
    ...allNames(step.goal),
  ].map<[() => Term, string]>((n) => [() => cnst(n), n]);

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
    .map<[() => Term, string]>(([, t]) => [() => t, termToTex(t, 0)]);

  const options: [() => Term, string][] = [
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
