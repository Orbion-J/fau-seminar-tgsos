#import "@preview/touying:0.6.1": *
#import themes.metropolis: *
#import "@preview/ctheorems:1.1.3": *
// #import "@preview/numbly:0.1.0": numbly
#import "@preview/curryst:0.5.0": rule, prooftree
#import "@preview/fletcher:0.5.6" as fletcher: diagram, node, edge


#show list.item: it => {
  // The generated terms is not tight
  // So setting `par.spacing` is to set the result lists' spacing
  let spacing = if list.spacing != auto {
    enum.spacing
  } else if enum.tight {
    par.leading
  } else {
    par.spacing
  }
  set par(spacing: spacing)

  let current-marker = if type(list.marker) == array {
    list.marker.at(0)
  } else {
    list.marker
  }

  context {
    let hanging-indent = measure(current-marker).width + terms
      .separator
      .amount
    set terms(hanging-indent: hanging-indent)
    if type(list.marker) == array {
      terms.item(
        current-marker,
        {
          // set the value of list.marker in a loop
          set list(marker: list.marker.slice(1) + (list.marker.at(0),))
          it.body
        },
      )
    } else {
      terms.item(current-marker, it.body)
    }
  }
}

#show: metropolis-theme.with(
  aspect-ratio: "16-9",
  footer: self => [#self.info.title -- Robin Jourde],
  config-info(
    title: [Trace Equivalence in Abstract GSOS],
    subtitle: [Oberseminar des Lehrstuhls für Theoretische Informatik],
    author: [*Robin Jourde*#footnote[ENS de Lyon -- robin.jourde\@ens-lyon.fr], Stelios Tsampas, Sergey Goncharov, Henning Urbat, Pouya Partow, Jonas Forster],
    date: [14th January 2025],
    // institution: [],
    // logo: [],
  ),
//   config-common(handout: true)
)

#show footnote.entry: set text(size:15pt)
#set footnote.entry(separator: none)

#set heading(numbering: "1.1")
// #set heading(numbering: numbly("{1}.", default: "1.1"))

#show outline.entry: it => it.indented(it.prefix(), it.body())

// Theorems configuration by ctheorems
#show: thmrules.with(qed-symbol: $square$)
#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let corollary = thmplain(
  "corollary",
  "Corollary",
  base: "theorem",
  titlefmt: strong
)
#let definition = thmbox("definition", "Definition", inset: (x: 1.2em, top: 1em))
#let example = thmplain("example", "Example").with(numbering: none)
#let remark = thmplain("remark", "Remark").with(numbering: none)
#let proof = thmproof("proof", "Proof")

#let onerule(..r) = prooftree(vertical-spacing:0.3em, rule(..r))

#let fmultimap = math.class("relation", context box(
  baseline: -0.1em,
  inset: (left: 0.075em, right: 0.061em),
  align(horizon, stack(dir: ltr,
    line(length: 0.512em, stroke: (paint: text.fill, thickness: 0.045em, cap: "round")),
    circle(radius: 0.15em, fill: text.fill)
  ))
))


#title-slide()

= Outline <touying:hidden>

#outline(title: none, indent: 2em, depth: 2)

= Preliminaries

== GSOS

- a *framework* for specifying reduction rules and semantics #pause

	$->$ rule format #pause

- given a *syntax* (with endofunctor $Sigma$) #pause

#example[
	Set of operations $cal(O)$ with arity map $"ar" : cal(O) -> NN$, $Sigma X = sum_(sigma in cal(O)) X^("ar" sigma)$
] #pause

#example[
	$t ::= 0 | a.t thick forall a in A | t + t | med ? t #pause ~~> Sigma X = 1 + A times X + X^2 + X$ #pause

	Eg. for $a,b,c,tau in A$ : $a.(b.a.0+ med?tau .a.c.0) #pause = a(b a+ med ?tau a c)$
] #pause

- *behaviour* (with endofunctor $H$) #pause

#example[
	$x$ *terminates* ($x arrow.b$) or *progresses* to $x'$ with label $a in A$ ($x ->^a x'$) #pause $~~> H X = cal(P)(1+A times X)$
]

---

- $k : X -> H X$ a *$H$-coalgebra* $-->$ set equipped with semantics #pause

#example[
	Let $k : X -> H X$, for $x in X$, $x arrow.b med <=> * in k(x)$ and $x ->^a x' <=> (a, x') in k(x)$
] #pause


// #align(center)[#grid(columns:3,column-gutter:1em,
// 	[#proof-tree(horizontal-spacing:0.3em,
// 			rule(
// 				$sigma(x_1 ... x_n) ->^b u[x_1...x_n, y_i...]$,
// 				${ x_i ->^(a_i) y_i }_(i in I)$,
// 				${ x_i arrow.b }_(i in.not I)$,
// 			)
// 		)],
// 		[or],
// 		[#proof-tree(horizontal-spacing:0.3em,
// 			rule(
// 				$sigma(x_1 ... x_n) arrow.b$,
// 				${ x_i ->^(a_i) y_i }_(i in I)$,
// 				${ x_i arrow.b }_(i in.not I)$,
// 			)
// 		)]
// )]

- *GSOS rules*

\

#align(center)[#grid(columns:3,column-gutter:1em,
		onerule(
			$sigma(x_1 ... x_n) ->^b u[x_1...x_n, y_(i,k)...]$,
			${ x_i ->^(a_(i,k)) y_(i,k) }_(i in I, k in K_i)$,
			${ x_j arrow.b }_(j in J)$,
		),
		[or],
		onerule(
			$sigma(x_1 ... x_n) arrow.b$,
			${ x_i ->^(a_(i,k)) y_(i,k) }_(i in I, k in K_i)$,
			${ x_j arrow.b }_(j in J)$,
		)
)]

\

with $sigma in cal(O), n = "ar" sigma, u in Sigma^*, a_(i,k), b in A, I, J, K_i subset [|1, n|]$

#slide(title:"A full example")[

- syntax: $t ::= 0 | a.t thick forall a in A | t + t | med ? t$ #pause

- rules
#align(center)[
	#grid(columns:6, gutter: 1.5em,
		uncover("3-", onerule($0 arrow.b$)),
		uncover("4-",onerule(name:$forall a$, $a.t ->^a t$)),
		uncover("5-",onerule(
			name:$forall a$,
			$t + u ->^a t'$,
			$t ->^a t'$
		)),
		uncover("5-", onerule(
			name:$forall a$,
			$t + u ->^a u'$,
			$u ->^a u'$
		)),
		uncover("5-", onerule(
			$t +u arrow.b$,
			$t arrow.b$,
			$u arrow.b$
		)),
		uncover("6-", onerule(
			$? t ->^tau t' + t''$,
			$t ->^tau t'$,
			$t ->^tau t''$,
		))
	)
] 

#align(center)[ 
	#uncover("7-",diagram(spacing:(0.5em,1.5em),
		node((1, 0), [$a(b+c)$]), edge($a$, "->"),
		node((1, 1), [$b+c$]), edge($b$, "->"), edge((2,2), $c$, "->"),
		node((0, 2), [$0$]),
		node((2, 2), [$0$])
	)) #h(3em) 
	#uncover("8-", diagram(spacing:(0.5em, 1.5em),
		node((1, 0), [$a b+a c$]), edge($a$, "->"), edge((2,1), $a$, "->"),
		node((0, 1), [$b$]), edge($b$, "->"),
		node((0, 2), [$0$]),
		node((2, 1), [$c$]), edge($c$, "->"),
		node((2, 2), [$0$])
	)) #h(3em) 
	#uncover("9-", diagram(spacing:(0.5em, 1.5em),
		node((1, 0), [$?(tau a+tau b)$]), edge($tau$, "->"),
		node((1, 1), [$a+b$]), edge($a$, "->"), edge((2,2), $b$, "->"),
		node((0, 2), [$0$]),
		node((2, 2), [$0$])
	))
]
]

== *Abstract* GSOS

- any syntax functor $Sigma$ and behaviour functor $H$ #pause

- rules $~~>$ a *natural transformation* $rho_X : Sigma (X times H X) -> H Sigma^* X$ #pause

#example[
	For the previous example without $?$ : $Sigma X = 1 + A times X + X^2$, 
	$ rho : 1 + A times (X times cal(P)(1 + A times X)) + (X times cal(P)(1 + A times X))^2 -> cal(P)(1 + A times Sigma^* X) $ #pause

	- $rho(*) = { * }$
	#only("4", align(center, onerule($0 arrow.b$))) #pause

	- $rho((a, t, T)) = { (a,t) }$
	#only("5", align(center, onerule(name:$forall a$, $a.t ->^a t$))) #pause

	- $rho( (t, T), (u, U) ) = { (a, t') | forall (a,t') in T } union uncover("7-", { (a, u') | forall (a, u') in U } union ) uncover("8-", { * | * in T and * in U } )$
	#only("6", align(center)[
		#grid(columns:1, gutter: 3em,
			onerule(
				name:$forall a$,
				$t + u ->^a t'$,
				$t ->^a t'$
			)
		)
	])
	#only("7", align(center)[
		#grid(columns:2, gutter: 3em,
			onerule(
				name:$forall a$,
				$t + u ->^a t'$,
				$t ->^a t'$
			),
			onerule(
				name:$forall a$,
				$t + u ->^a u'$,
				$u ->^a u'$
			)
		)
	])
	#only("8", align(center)[
		#grid(columns:3, gutter: 3em,
			onerule(
				name:$forall a$,
				$t + u ->^a t'$,
				$t ->^a t'$
			),
			onerule(
				name:$forall a$,
				$t + u ->^a u'$,
				$u ->^a u'$
			),
			onerule(
				$t +u arrow.b$,
				$t arrow.b$,
				$u arrow.b$
			)
		)
	])

]

== Trace & Kleisli categories

- *trace* of a term $t$: $"tr" t =$ set of words of $A^*$ that can be produced by $t$#pause, defined by coinduction

$ epsilon in "tr" t <=> t arrow.b #pause wide a.w in "tr" t <=> t ->^a u and w in "tr" u $ #pause

#example[
	$"tr" a(b+c) = pause { a b, a c }$, #pause $"tr" (a b + a c) = pause { a b, a c}$, #pause $"tr" (a + b ?c) = pause { a }$
	#meanwhile
	#align(center)[
		#only("4-5",diagram(spacing:(0.5em,1.5em),
			node((1, 0), [$a(b+c)$]), edge($a$, "->"),
			node((1, 1), [$b+c$]), edge($b$, "->"), edge((2,2), $c$, "->"),
			node((0, 2), [$0$]),
			node((2, 2), [$0$])
		)) 
		#only("6-7", diagram(spacing:(0.5em, 1.5em),
			node((1, 0), [$a b+a c$]), edge($a$, "->"), edge((2,1), $a$, "->"),
			node((0, 1), [$b$]), edge($b$, "->"),
			node((0, 2), [$0$]),
			node((2, 1), [$c$]), edge($c$, "->"),
			node((2, 2), [$0$])
		))	
		#only("8-9", diagram(spacing:(0.5em, 1.5em),
			node((1, 0), [$a + b?c$]), edge($a$, "->"), edge((2,1), $b$, "->"),
			node((0, 1), [$0$]),
			node((2, 1), [$? c$]), edge("-/->"),
			node((2, 2), [])
		))
	]
] #pause

- recall $H X = cal(P)(1 + A times X)$ #pause $= T B X$ 
	- $T = cal(P)$ *effectful* behaviour #uncover("12-", [$~>$ powerset : non-determinism])
	- $B = 1 + A times X$ *pure* behaviour #pause $~>$ words : $A^*$ (initial $B$-algebra) #pause

#only("10-")[
- $tr t in cal(P)(A^*)$
]
--- 

Trace *abstractly*#pause
- in the *Kleisli category* of $T$ #pause 
$ A in "Kl"(T) &<=> A in CC wide wide 
A fmultimap B in "Kl"(T) &<=> A -> T B in CC $ #pause

- $A^*$ is the final $B$-coalgebra in $"Kl"(T)$ #pause
$ zeta : A^* fmultimap B A^* "or" A^* -> T B A^* wide wide zeta(epsilon) = {*}, quad zeta (a.w) = {(a,w)} $ #pause

- for any $k : X fmultimap B X$, 
#align(center, diagram(
	node((0,0), $X$), edge($k$, "-*"), edge((0,1), $"tr"_k$, "--*"),
	node((1,0), $B X$), edge((1,1), $B"tr"_k$, "--*", label-side:left),
	node((0,1), $A^*$), edge($zeta$, "-*"),
	node((1,1), $B A^*$)
))

== Trace-GSOS

- GSOS rule
#only("1")[$ rho : Sigma (X times H X) -> H Sigma^* X $]#only("2-")[$ rho : Sigma (X times T B X) ->  T B Sigma^* X $] #pause #pause
- *Trace*-GSOS rule
#only("-4")[$ rho : Sigma (X times B X) ->  T B Sigma^* X $] #only("5-")[$ rho : Sigma (X times B X) fmultimap B Sigma^* X $]
#pause $~>$ only pure observations #pause #pause

- Rules observe each variable *once and only once* #pause

#example[
	#align(center)[
		#grid(columns:4, gutter: 1.5em,
			[#onerule(
				$? t ->^tau t' + t''$,
				$t ->^tau t'$,
				$t ->^tau t''$,
			) #emoji.face.unhappy],
			[#onerule(name:$forall a$, $a.t ->^a t$) #emoji.face.unhappy],
			[#onerule(
				name:$forall a, b$,
				$a.t ->^a t$,
				$t ->^b t'$
			) #emoji.face.cool],
			[#onerule(
				name:$forall a$,
				$a.t ->^a t$,
				$ t arrow.b$
			) #emoji.face.cool]
		)
	]
]

== Trace equivalence & congruence

- *trace equivalence*: #pause $t equiv_"tr" u <=> "tr" t = "tr" u$ #pause

#example[
	Recall $"tr" a(b+c) = { a b, a c } = "tr" (a b + a c)$.
	#only("-5", align(center)[
		#diagram(spacing:(0.5em,1.5em),
			node((1, 0), [$a(b+c)$]), edge($a$, "->"),
			node((1, 1), [$b+c$]), edge($b$, "->"), edge((2,2), $c$, "->"),
			node((0, 2), [$0$]),
			node((2, 2), [$0$])
		) #h(2em) #diagram(spacing:(0.5em, 1.5em),
			node((1, 0), [$a b+a c$]), edge($a$, "->"), edge((2,1), $a$, "->"),
			node((0, 1), [$b$]), edge($b$, "->"),
			node((0, 2), [$0$]),
			node((2, 1), [$c$]), edge($c$, "->"),
			node((2, 2), [$0$])
		) ] ) #pause
	$a(b+c) equiv_"tr" a b + a c$ #pause but not bisimilar $~>$ $equiv_"tr"$ coarsest
] #pause

- *congruence*: #pause $forall sigma, (forall i, t_i equiv u_i) => sigma(t_1 ... t_n) equiv sigma(u_1...u_n)$ #pause

- prove $"tr"(sigma(t_1...t_n)) = [|sigma|]("tr" t_1 ... "tr" t_n)$ #pause

#only("6-")[
#align(center, diagram(
	node((0,0), $Sigma X$), edge($i$, "-*"), edge((0,1), $Sigma "tr"_k$, "-*"), edge((1,1), label:"?", label-side:center, stroke:0pt),
	node((1,0), $X$), edge($k$, "-*"), edge((1,1), $"tr"_k$, "-*"), edge((2,1), label:emoji.checkmark, label-side:center, stroke:0pt),
	node((2,0), $B X$), edge((2,1), $B "tr"_k$, "-*", label-side:left),
	node((0,1), $Sigma A^*$), edge($[|-|]$, "-*", label-side:right),
	node((1,1), $A^*$), edge($zeta$, "-*", label-side:right),
	node((2,1), $B A^*$)
))]

== Strong and affine monads

- *strong monad*: $"st"_(X,Y) : X times T Y -> T(X times Y)$ #pause $~~>$ $"st"' : T X times Y -> T(X times Y)$ #pause

- double strength $"dst" : T X times T Y ->^("st") T (T X times Y) ->^(T "st"') T^2 (X times Y) ->^mu T ( X times Y)$ #pause (and $"dst"'$) #pause

- *affine monad*: $T X times T Y ->^"dst" T (X times Y) -->^(angle.l T pi_1, T pi_2 angle.r) T X times T Y = "id"$ or $eta_1 : 1 ->^tilde.eq T 1 $ #pause

- *affine part*: greatest affine submonad #pause

#example[
	- Powerset $cal(P) ~~> cal(P)_"ne"$ #pause
	- (Sub)distribution $cal(S) ~~> cal(D)$ #pause
		with $cal(D)X = { sum_(i in I) p_i x_i | sum p_i = 1, x_i in X, I "finite"}$ and $cal(S)X = { sum_(i in I) p_i x_i | sum p_i <= 1, x_i in X, I "finite" }$ #pause
	- Maybe $- + 1 ~~> "Id"$
]

= Result

== The theorem

#theorem[
	Let $CC$ be a cartesian category,#pause $T$ be a strong *affine* _effectful_ monad, #pause $B$ a _behaviour_ endofunctor that extends to $"Kl"(T)$, #pause $Sigma$ a _syntax_ endofunctor that extends to $"Kl"(T)$ with all free objects ($Sigma^* X$), #pause let $zeta : Z fmultimap B Z$ be the final $overline(B)$-coalgebra (with $exists z, zeta = eta compose z$) and #pause let $rho : Sigma (X times B X) -> T B Sigma^* X$ be a natural transformation _representing Trace-GSOS rules_ #pause such that $rho$ is *smooth* and is a map of distributive laws, #pause then trace equivalence is a congruence.
]

== Sketch of the proof

- Recall
#align(center, diagram(
	node((0,0), $Sigma^* X$), edge($i$, "-*"), edge((0,1), $Sigma^* "tr"_k$, "-*"),
	node((1,0), $X$), edge((1,1), $"tr"_k$, "-*", label-side:left),
	node((0,1), $Sigma^* Z$), edge($[|-|]$, "-*", label-side:right),
	node((1,1), $Z$),
)) #pause
- define $[|-|]$ : semantics of $Z$ + induction + trace #pause
- $Sigma^* X fmultimap B Sigma^* X$ (with $rho^*$) #pause and $Z fmultimap B Z$ #pause
- show $overline(B)$-coalgebra morphisms #pause
- $"tr" compose i quad checkmark$ #pause
- $[|-|] compose Sigma^*"tr"$ more complicated : naturality + smoothness + map of distributive law of $rho^*$ #pause
#remark[
	need $"dst"$
]

== Focus on hypothesis : Smoothness

#example[ $t::= 0 | a.t | t + t | med ? t | ! t$ with the previous rules for $0, a., +$ and #pause
	#align(center)[#grid(columns:2,gutter:1.5em,
		onerule(
			name:$forall a$,
			$! t ->^a ? t'$,
			$t ->^a t'$
		),
		onerule(
			name:$forall a$,
			$? t ->^a t + t'$,
			$t ->^a t'$
		),
	)
	] #pause
	#diagram(spacing:(0.5em,1.5em),
		node((2,0), $!a(b+c)$), edge($a$, "->"),
		node((2,1), $?(b+c)$), edge($b$, "->"), edge((3,2),$c$, "->"),
		node((1,2), $(b+c)+0$), edge($b$, "->"), edge((1,3), $c$, "->"),
		node((0,3), $0$),
		node((1,3), $0$),
		node((3,2), $(b+c)+0$), edge($b$, "->"), edge((4,3), $c$, "->"),
		node((3,3), $0$),
		node((4,3), $0$),
	) #h(3em) #pause #pause
	#diagram(spacing:(0.5em,1.5em),
		node((2,0), $!(a b + a c)$), edge($a$, "->"), edge((3,1), $a$, "->"),
		node((1,1), $?b$), edge($b$, "->"),
		node((1,2), $b+ 0$), edge($b$, "->"),
		node((0,3), $0$),
		node((3,1), $?c$), edge($c$, "->"),
		node((3,2), $c + 0$), edge($c$, "->"),
		node((4,3), $0$),
	) #pause
	#meanwhile
	#uncover("4-")[$tr !a(b+c) = { a b, a c, a b b, underline(a b c), underline(a c b), a c c }$] #uncover("6-")[$eq.not { a b, a c, a b b, a c c } = tr !(a b + a c)$]
]

// ---

// #example[ $t::= 0 | a.t | t + t | med ? t | ! t$ with the previous rules for $0, a., +$ and
// 	#align(center)[#grid(columns:2,gutter:1.5em,
// 		onerule(
// 			name:$forall a$,
// 			$! t ->^a ? t'$,
// 			$t ->^a t'$
// 		),
// 		onerule(
// 			$? t ->^tau t$,
// 			$t ->^tau t'$
// 		)
// 	)
// 	] #pause
// 	#align(center)[#diagram(spacing:(0.5em,1.5em),
// 		node((1,0), $!a(b+tau)$), edge($a$, "->"),
// 		node((1,1), $?(b+tau)$), edge($tau$, "->"), 
// 		node((1,2), $b + tau$), edge($b$, "->"), edge((2,3), $tau$, "->"),
// 		node((0,3), $0$),
// 		node((2,3), $0$)
// 	) #h(3em) #pause #pause
// 	#diagram(spacing:(0.5em,1.5em),
// 		node((1,0), $!(a b + a tau)$), edge($a$, "->"), edge((2,1), $a$, "->"),
// 		node((0,1), $?b$), edge((0,2),"-/->"),
// 		node((0,2), ""),
// 		node((2,1), $?tau$), edge($tau$, "->"),
// 		node((2,2), $tau$), edge($tau$, "->", label-side:left),
// 		node((2,3), $0$, stroke:1pt),
// 	) #pause]
// 	#meanwhile
// 	#uncover("3-")[$tr !a(b+tau) = { underline(a tau b), a tau tau }$]
// 	#uncover("5-")[$eq.not { a tau tau } = tr !(a b + a tau)$] 
// ] #pause
// $-->$ observations that are "not used" #emoji.face.unhappy

// ---

// - *smoothness* #pause
// 	- *linear*: if $x_i -> x_i'$ then not $x_i$ and $x_i'$ in the target #pause
// 	- if $x_i$ in the target, the observation on $x_i$ is *irrelevant* ie. any other observation could have been done (the same rule for each other possible observation exists) #pause

// - *abstract smoothness*
// #grid(columns:(60%,40%),align:(left, center),
// 	diagram(spacing:(1em, 1.5em),
// 		node((0,0), $Sigma T(X times B X)$), edge($angle.l T pi_1, T pi_2 angle.r$, "->"),
// 			edge((0,1), $lambda$, "->"), edge((0,0), (0,-1), (2,-1), (2,0), $"mix"$, "-->"),
// 		node((1,0), $Sigma (T X times T B X)$), edge($"dst"$, "->"),
// 		node((2,0), $Sigma T (X times B X)$), edge((2,1), $lambda$, "->"),
// 		node((0,1), $T Sigma (X times B X)$), edge($T rho$, "->"),
// 		node((0,2), $T^2 B Sigma^* X$), edge($mu$, "->"),
// 		node((1,2), $T B Sigma^* X$),
// 		node((2,1), $T Sigma (X times B X)$), edge($T rho$, "->"),
// 		node((2,2), $T^2 B Sigma^* X$), edge((1,2), $mu$, "->")
// 	),
// 	[#pause $Phi(rho)(sigma)("mix" X_1 ... "mix" X_n) = Phi(rho)(sigma)(X_1 ... X_n)$ \ where $X_i subset X times B X$]
// )

// ---

// - need smoothness *for $rho^*$* (terms with more than one layer) #pause
// #example[$t::= 0 | a.t | med ? t$ with the following smooth rules #pause
// 	#align(center)[
// 		#grid(columns:4, gutter: 1.5em,
// 			onerule($0 arrow.b$),
// 			onerule(
// 				name:$forall a, b$,
// 				$a.t ->^a t$,
// 				$t ->^b t'$
// 			),
// 			onerule(
// 				name:$forall a$,
// 				$a.t ->^a t$,
// 				$ t arrow.b$
// 			),
// 			onerule(
// 				$? t ->^tau t'$,
// 				$t ->^tau t'$
// 			)
// 		)
// 	] #pause
// 	let $X_1 = {t ->^tau t', u ->^a u'}$ #pause then $"mix" X_1 = { t ->^tau t', t ->^a u', u ->^tau t', u ->^a u'}$ #pause

// 	#grid(columns: 5, gutter: 3em,
// 		uncover("6-",onerule(
// 			$b. ? t ->^b ? t$ ,
// 			rule(
// 				$? t ->^tau t'$,
// 				$t ->^tau t' in X_1$
// 			)
// 		)) ,
// 		uncover("6-", onerule(
// 			$b. ? u arrow.not$ ,
// 			rule(
// 				$? u arrow.not$,
// 				$u ->^tau ? in.not X_1$
// 			)
// 		)) ,
// 		[],
// 		uncover("8-",onerule(
// 			$b. ? t ->^b ? t$ ,
// 			rule(
// 				$? t ->^tau t'$,
// 				$t ->^tau t' in "mix" X_1$
// 			)
// 		)) ,
// 		uncover("8-", onerule(
// 			$b. ? u ->^b ? u$ ,
// 			rule(
// 				$? u ->^tau t'$,
// 				$u ->^tau t' in "mix" X_1$
// 			)
// 		))
// 	)
// 	#pause $Phi(rho^*)(b.?x_1)(X_1) = { ->^b ? t } pause pause eq.not { ->^b ? t, ->^b ? u } = Phi(rho^*)(b.?x_1)("mix" X_1)$ #pause $-->$ the *stuck* computation is messing with smoothness #emoji.face.unhappy
// ]

== Focus on hypothesis : Affineness

#theorem[If $T$ is an *affine* monad then the smoothness of $rho$ entails the smoothness of $rho^*$.] #pause

- affine part of $cal(P)$ is $cal(P)_"ne"$ $-->$ no stuckness ! #pause

- at the level of rules: give a semantics to *every situation*, nothing unspecified #pause
#example[
	#align(center)[
		#grid(columns:4, gutter: 1.5em,
			onerule(
				$? t ->^tau t'$,
				$t ->^tau t'$
			),
			[#pause $+$],
			[#only("-5",onerule(
				name:$forall a eq.not tau$,
				$?t med ...$,
				$t ->^a t'$
			)) #only("6-",onerule(
				name:$forall a eq.not tau$,
				$?t arrow.b$,
				$t ->^a t'$
			))],
			[#only("-5",onerule(
				$?t med ...$,
				$t arrow.b$
			)) #only("6-",onerule(
				$?t arrow.b$,
				$t arrow.b$
			))],
		)
	]
	need to have some semantics #pause eg. termination $arrow.b$
]

== And for non affine monads ?

- still under investigation #emoji.construction #pause

- idea 1: add an *extra sink state* $bot$ for stuck computations #pause

- idea 2: map stuckness to *explicit termination* (cf. previous example) #emoji.siren change of semantics #pause

$-->$ Can we get back information on the original system ?

= Conclusion

---

- For an affine monadic effect, under reasonable assumptions, trace equivalence is a congruence #emoji.face.party ! #pause

- Can we do better ? #pause Can we find a good reduction to the affine case for non affine monads ? #pause

- Thank you all for welcoming me in the chair #emoji.heart

#align(center)[
	#text(font:"z003", size: 42pt)[\~ The End \~]
]

#align(right)[
	#text(fill:gray, size:14pt)[Powered by #link("https://typst.app/")[Typst]]
]