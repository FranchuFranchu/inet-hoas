# Inet HOAS

HOAS representation for interaction nets.

Copied from Discord:
```txt
I came up with this representation while I was thinking about how a "reflect" node would look like. The agent would take in a normal-form net and output a representation.

Previously, all the interaction-type-theory typecheckers were an inet reduction engine + an external program that reads the output and decides whether it's well typed or not according to a rule. However, if we have a reflect node, we could implement the part that decides whether it's well typed or not with inets only, without an external layer.

One of the challenges was figuring out how the reflected representation would look like. Since the reflect node has to be local, then the representation has to be local too. That's why variable names or indices are not useful here. 

I figured out that the best way to represent variables is simply wires, which in SIC are scopeless lambdas. If the nets we're reading back are polarized, then one side of the variable can be the binder side and the other one can be the user side.

I posted this here and T6 called it "inet hoas", which is a really good name because it opens up possibilities I hadn't thought about before. 

Most ICC implementations we wrote in HVM were based on λ-calculus readback representation. This is very good and carried us far but the problem is that it's an imperfect translation of the underlying interaction nets. If we use inet-hoas for a new ICC checker, then we'll be closer to its interaction net foundations and perhaps some things will be clearer.
```