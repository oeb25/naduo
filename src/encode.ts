export const temp = {};
// const encodeSteps = (steps: Step[]) => {
//   return steps.map(encodeStep).join(":");
// };
// const encodeStep = (step: Step) => {
//   const rule = step.assumptions.find((a) => equal(a, step.goal))
//     ? "OK"
//     : step.rule?.replaceAll("_", "");
//   return `${rule}{${encodeTerm(step.goal)}}[${step.assumptions
//     .map((a) => encodeTerm(a))
//     .join(",")}]`;
// };
// const encodeTerm = (term: Term, inPre = false): string => {
//   switch (term.type) {
//     case "hole":
//       return "hole";
//     case "wrapper":
//       return "wrapper";
//     case "falsify":
//       return "falsify";
//     case "imp":
//       return `Imp{${encodeTerm(term.a)}}{${encodeTerm(term.b)}}`;
//     case "fun":
//       const ann = inPre ? "Fun" : "Pre";
//       if (term.args.length == 0) return `${ann}{${term.name}}{}`;
//       else
//         return `${ann}{${term.name}}{[${term.args
//           .map((a) => encodeTerm(a, true))
//           .join(",")}]}`;
//     case "con":
//       return `con`;
//     case "dis":
//       return `dis`;
//     case "exi":
//       return `exi`;
//     case "uni":
//       return `uni`;
//     case "quant":
//       return "quant";
//     // return `x${term.depth}`;
//   }
// };
// console.clear();
// const src = `ImpI{Imp{Pre{A}{}}{Pre{A}{}}}[]:{OK{Pre{A}{}}[Pre{A}{}]}`;
// console.log(
//   src
//     .split("")
//     .reduce<[string, number]>(
//       ([acc, d], c) =>
//         c == "{" || c == "["
//           ? [acc + c + "\n" + " ".repeat(d + 1), d + 1]
//           : c == "}" || c == "]"
//           ? [acc + "\n" + " ".repeat(d - 1) + c, d - 1]
//           : [acc + c, d],
//       ["", 0]
//     )[0]
// );
// console.log(
//   encodeSteps([
//     {
//       rule: "Imp_I",
//       assumptions: [],
//       goal: imp(fun("A", [cnst("b")]), cnst("b")),
//     },
//     {
//       rule: null,
//       assumptions: [fun("A", [cnst("b")])],
//       goal: cnst("b"),
//     },
//   ])
// );
