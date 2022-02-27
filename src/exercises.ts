import {
  cnst,
  con,
  dis,
  exi,
  falsity,
  fun,
  imp,
  quant,
  Term,
  uni,
} from "./logic";

const A = (...args: Term[]) => (args.length == 0 ? cnst("A") : fun("A", args));
const c = cnst("c");
const B = cnst("B");
const C = cnst("C");

export const exercises = [
  imp(A(), A()),
  imp(falsity(), falsity()),
  imp(falsity(), A()),
  imp(imp(A(), B), imp(A(), B)),
  imp(A(), imp(imp(A(), B), B)),
  imp(con(A(), imp(A(), B)), B),
  imp(con(A(c), imp(A(c), uni(A(quant(1))))), uni(A(quant(1)))),
  imp(uni(A(quant(1))), A(c)),
  imp(A(c), exi(A(quant(1)))),
  imp(A(), imp(B, A())),
  imp(imp(A(), imp(B, C)), imp(imp(A(), B), imp(A(), C))),
  imp(A(), imp(imp(A(), falsity()), falsity())),
  imp(imp(imp(A(), falsity()), falsity()), A()),
  imp(con(A(), B), imp(C, con(A(), C))),
  imp(dis(imp(A(), falsity()), imp(B, falsity())), imp(con(A(), B), falsity())),
  imp(uni(uni(A(quant(2), quant(1)))), uni(A(quant(1), quant(1)))),
  imp(uni(A(quant(1))), exi(A(quant(1)))),
  exi(imp(A(quant(1)), uni(A(quant(1))))),
];
