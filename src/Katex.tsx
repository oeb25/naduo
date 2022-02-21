import * as React from "react";
import katex from "katex";
import "katex/dist/katex.min.css";

export const Katex: React.FC<{ src: string }> = ({ src }) => {
  const [ref, setRef] = React.useState(null as null | HTMLSpanElement);

  React.useEffect(() => {
    if (ref) katex.render(src, ref, { trust: true });
  }, [src, ref]);

  return (
    <span
      ref={(x) => {
        setRef(x);
      }}
    ></span>
  );
};
