#import "@preview/touying:0.6.1": *
#import themes.metropolis: *
#import "@preview/curryst:0.5.0": rule, prooftree
#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge
#import "@preview/great-theorems:0.1.2" : *

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


#let mathcounter = counter("mathcounter")

#show: metropolis-theme.with(
  aspect-ratio: "16-9",
  footer: self => [#self.info.title -- Robin Jourde],
  config-info(
    title: [(Abstract) GSOS for Trace Equivalence],
    subtitle: [Séminaire LIMD],
    author: [*Robin Jourde*#footnote[ENS de Lyon -- robin.jourde\@ens-lyon.fr], Stelios Tsampas#footnote[Syddansk Universitet], Sergey Goncharov#footnote[University of Birmingham]<uob>, Henning Urbat#footnote[*Friedrich-Alexander-Universität Erlangen-Nürnberg*]<fau>, Pouya Partow@uob, Jonas Forster@fau],
    date: [27 Mars 2025],
    // institution: [],
    // logo: [],
  ),
  config-common(
		frozen-counters: (mathcounter, ),
		// handout: true,
	)
)

#show footnote.entry: set text(size:15pt)
#set footnote(numbering:"*")
#set footnote.entry(separator: none)

#set heading(numbering: "1.1")

#show outline.entry: it => it.indented(it.prefix(), it.body())

#show outline.entry.where(level : 2) : set text(size: 10pt)

// Theorem config by great-theorem
#show: great-theorems-init
#let theorem = mathblock(
	blocktitle: "Theorem",
	counter: mathcounter,
	fill:rgb("eeffee"),
	inset:1em,
	radius:0.5em,
)
#let example = mathblock(
  blocktitle: "Example",
	fill:rgb("fffedd"),
	inset:1em,
	radius:0.5em,
)
#let remark = mathblock(
  blocktitle: "Remark",
)
#let proof = proofblock()

#let onerule(..r) = prooftree(vertical-spacing:0.3em, rule(..r))

#let fmultimap = math.class("relation", context box(
  baseline: -0.1em,
  inset: (left: 0.075em, right: 0.061em),
  align(horizon, stack(dir: ltr,
    line(length: 0.512em, stroke: (paint: text.fill, thickness: 0.045em, cap: "round")),
    circle(radius: 0.15em, fill: text.fill)
  ))
))

#let rel = math.class("relation", [⇸])

#title-slide()

= Outline <touying:hidden>


#outline(title: none, indent: 2em, depth: 2)

= Trace equivalence for concrete systems

== Processes and LTSs 

- study the *behaviour of processes* #pause
- running example: *labelled transition systems* (LTS) with explicit termination #pause
	- set of actions/labels $A$ #pause
	- set of processes/states $X$ with some operations
		- a special state $0 in X$
		- for each action $a in A$ and process $x in X$, a process $a.x in X$ #pause
		- and at will: a binary operation $+$, unary operations $!$, $?$ ... #pause
#example[
	For $a,b,c,d in A$
	- $0$ #h(1fr) $a.0$#uncover("9-")[$med = a$] #h(1fr) $d.a.0$#uncover("9-")[$med = d a$] #pause
	- $a.0 + b.c.0$#uncover("9-")[$med = a + b c$] #h(1fr) $?(c.d.0)$#uncover("9-")[$med = med? c d$] #h(1fr) #pause
	- $a.(b.a.0+ med?(d.a.c.0))$#uncover("9-")[$med = a(b a+ med? d a c)$]
]#pause

---

- *behaviour* of a process $x$:  #pause
	- can progress emitting a label $a in A$ and continuing with process $y$: "$x->^a y$" #uncover("3-")[$~> (a,y) in k(x)$ ]
	- or terminate: "$x arrow.b$" #uncover("3-")[$~> star in k(x)$] #pause
	- collect everything in a map $k : X -> cal(P) (A times X + {star})$ #pause

- given by the *rules*:
#align(center)[
	#grid(columns:6, gutter: 1.5em,
		uncover("4-", onerule($0 arrow.b$)),
		uncover("5-",onerule(name:$forall a$, $a.t ->^a t$)),
		uncover("6-",onerule(
			name:$forall a$,
			$t + u ->^a t'$,
			$t ->^a t'$
		)),
		uncover("6-", onerule(
			name:$forall a$,
			$t + u ->^a u'$,
			$u ->^a u'$
		)),
		uncover("6-", onerule(
			$t +u arrow.b$,
			$t arrow.b$,
		)),
		uncover("6-", onerule(
			$t +u arrow.b$,
			$u arrow.b$,
		)),
	)
] 
--- 
#align(center)[
	#grid(columns:6, gutter: 1.5em,
		onerule($0 arrow.b$),
		onerule(name:$forall a$, $a.t ->^a t$),
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
		),
		onerule(
			$t +u arrow.b$,
			$u arrow.b$,
		),
	)
] 

#example[
	#align(center)[ 
		#uncover("2-",diagram(spacing:(0.5em,1.5em),
			node((1, 0), [$a(b+c)$]), edge($a$, "->"),
			node((1, 1), [$b+c$]), edge($b$, "->"), edge((2,2), $c$, "->"),
			node((0, 2), [$0$], stroke: 1pt),
			node((2, 2), [$0$], stroke: 1pt)
		)) #h(3em) 
		#uncover("3-", diagram(spacing:(0.5em, 1.5em),
			node((1, 0), [$a b+a c$]), edge($a$, "->"), edge((2,1), $a$, "->"),
			node((0, 1), [$b$]), edge($b$, "->"),
			node((0, 2), [$0$], stroke:1pt),
			node((2, 1), [$c$]), edge($c$, "->"),
			node((2, 2), [$0$], stroke: 1pt)
		)) #h(3em) 
		#uncover("4-", diagram(spacing:(0.5em, 1.5em),
			node((1, 0), [$0 + (a + a a)$], stroke:1pt), edge($a$, "->", label-pos: 80%), edge((2,1), $a$, "->", label-pos: 80%),
			node((0, 1), [$0$], stroke:1pt),
			node((2, 1), [$a$]), edge($a$, "->"),
			node((2, 2), [$0$], stroke:1pt)
		))
	]
]

== Program equivalences

- how to compare programs? what does it mean to be "the same" program? #pause
#example[
	$f(x) := x + x$ and $g(x) := 2 times x$
]#pause

- many different notions (linear time/branching time spectrum): bisimilarity, trace equivalence#pause

- important property: contextual equivalence and *congruence*
	$ (forall i, x_i tilde y_i) => sigma(x_1 .. x_n) tilde sigma(y_1 ... y_n) $#pause

#example[$x tilde y => a.x tilde a.y$, or $x_1 tilde y_1 and x_2 tilde y_2 => x_1 + x_2 tilde y_1 + y_2$]

== Trace and trace equivalence

- different flavors: partial vs. complete, finite vs. infinite #pause
- complete infinitary traces:
	$ "tr"(x) = union.big_(n in NN) { w in A^n mid(|) x ->^(w_1) x_1 ->^(w_2) ... ->^(w_n) x_n arrow.b } union { w in A^omega mid(|) x ->^(w_1) x_1 ->^(w_2) ... } subset.eq A^oo $
	Set of finite and infinite words with letters in $A$ corresponding to all possible (terminating or infinite) executions.#pause
#remark[
	$"tr"$ is the greatest map such that $epsilon ∈ "tr"(x) ⇔ x ↓$ and $a.w ∈ "tr"(x) ⇔ x→^a y ∧ w ∈ "tr"(y)$ ("_coalgebra morphism_")
]#pause
- trace equivalence: $x tilde_"tr" y <=> "tr"(x) = "tr"(y)$

---
$ "tr"(x) = union.big_(n in NN) { w in A^n mid(|) x ->^(w_1) x_1 ->^(w_2) ... ->^(w_n) x_n arrow.b } union { w in A^omega mid(|) x ->^(w_1) x_1 ->^(w_2) ... } $

#example[
	$"tr" a(b+c) = pause { a b, a c }$, #pause $"tr" (a b + a c) = pause { a b, a c}$, #pause $"tr" x = pause { a.b^omega }$
	#meanwhile
	#align(center)[
		#uncover("1-",diagram(spacing:(0.5em,1.5em),
			node((1, 0), [$a(b+c)$]), edge($a$, "->"),
			node((1, 1), [$b+c$]), edge($b$, "->"), edge((2,2), $c$, "->"),
			node((0, 2), [$0$], stroke:1pt),
			node((2, 2), [$0$], stroke:1pt)
		)) #h(1em) #box(uncover("4")[$tilde_"tr"$], height:7em) #h(1em)
		#uncover("3-", diagram(spacing:(0.5em, 1.5em),
			node((1, 0), [$a b+a c$]), edge($a$, "->"), edge((2,1), $a$, "->"),
			node((0, 1), [$b$]), edge($b$, "->"),
			node((0, 2), [$0$], stroke:1pt),
			node((2, 1), [$c$]), edge($c$, "->"),
			node((2, 2), [$0$], stroke:1pt)
		))	
		#only("5-")[#h(3em) #diagram(spacing:(1em, 1.5em),
			node((1, 0), [$x$]), edge($a$, "->"), edge((2,1), $c$, "->"),
			node((0, 1), [$y$]), edge((0,1), $b$, "->", bend:-130deg),
			node((2, 1), [$z$]), edge("-/->"),
			node((2, 2), [])
		)]
	]
] 

== Rule formats: GSOS

- a *framework* for reduction rules #pause $->$ rule format #pause

- given a *syntax* : set of operations $cal(O) = { 0, a. , b. , ..., +, !, ...}$ with arity map $"ar" : cal(O) -> NN$
	#pause

- *GSOS rules*
#v(0.5em)
#align(center)[#grid(columns:3,column-gutter:1em,
		onerule(
			$sigma(x_1 ... x_n) ->^b u$,
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
#v(0.5em)
with $sigma in cal(O), n = "ar" sigma, a_(i,k), b in A, I, J, K_i subset [|1, n|]$ and  $u$ complex term with variables in ${x_1...x_n, y_(i,k)...}$ #pause

- GSOS $=>$ bisimilarity is a congruence#footnote[D. Turi et G. Plotkin, « Towards a mathematical operational semantics », 1997]#pause, what about trace equivalence ?

== Trace-GSOS

- recall behaviour $k : X -> cal(P)(A times X + {star})$ #pause
	- $cal(P)$: *effectful* behaviour (non-determinism)
	- $A times \_ + {star}$: *pure* behaviour (emit labels or terminate) #pause
- *Trace*-GSOS rules 
#v(0.5em)
#align(center)[#grid(columns:3,column-gutter:1em,
		onerule(
			$sigma(x_1 ... x_n) ->^b u$,
			${ x_i ->^(a_(i)) y_i }_(i in I)$,
			${ x_j arrow.b }_(j in.not I)$,
		),
		[or],
		onerule(
			$sigma(x_1 ... x_n) arrow.b$,
			${ x_i ->^(a_(i)) y_(i) }_(i in I)$,
			${ x_j arrow.b }_(j in.not I)$,
		)
)]
#v(0.5em)
with $u$ complex term with variables in ${x_1...x_n, y_i...}$ with *at most one of $x_i\/y_i$ for each $i$* (_sublinearity_)#pause
#remark[only *pure* observations/premises#pause: observe each variable *once and only once* ]
	 
---

#example[
	#align(center)[
		#grid(columns:5, gutter: 1.5em,
			[#onerule(
				$? t ->^a t + t'$,
				$t ->^a t'$,
				$t ->^a t''$,
			) #emoji.face.unhappy],	
			[#onerule(
				$! t ->^a t + t$,
				$t ->^a t'$,
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
]#pause
#v(-0.5em)
- require 2 extra conditions on the set of rules: #pause
	- *affineness*: for each term, there is a least one rule that can apply #pause $~> k : X -> only("-4",cal(P)) #only("5-")[$cal(P)_"ne"$] (A times X + {star})$ #pause #pause
	- *smoothness*: $x_i$ in the target, the observation on $x_i$ is *irrelevant* ie. any other observation could have been done (the same rule for each other possible observation exists)

== Theorem 

#theorem[
	Let $cal(R)$ be a smooth and affine set of Trace-GSOS rules. Let $X$ be a set of terms equipped with behaviour $k : X -> cal(P)_"ne" (A times X + {star})$ induced by $cal(R)$. Then trace equivalence $tilde_"tr"$ is a congruence.
]#pause
#proof[
	Show that the trace of a complex term can be obtained from the traces of its subterms.#pause
	- consider complex terms with words of $A^oo$ as leaves, and behaviour induced by $cal(R)$ with $a.w ->^a w$ and $epsilon arrow.b$ #pause
	- extend the trace function of this system to maps $[|u|] : (cal(P)_"ne" A^oo)^n → cal(P)_"ne" A^oo$ for each complex term $u$ with $n$ free variables #pause
	- prove $"tr" u[t_1 ... t_n] = [|u|]("tr" t_1 ... "tr" t_n)$ by showing that both sides are maximal coalgebra morphisms
]

== Counter-examples

Affineness, smoothness and sublinearity are *necessary* #pause

=== Sublinearity 

#align(center)[#grid(columns:2,gutter:1.5em,
	onerule(
		name:$forall a$,
		$! t ->^a ? t'$,
		$t ->^a t'$
	),
	onerule(
		name:$forall a$
		,
		$? t ->^e t | t$,
		$t ->^a t'$
	),
)
] #pause
#align(center)[
	#diagram(spacing:(0em,1.2em),
		node((2,0), $!a(b+c)$), edge($a$, "->"),
		node((2,1), $?(b+c)$), edge($e$, "->"),
		node((2,2), $(b+c)|(b+c)$), edge($b b, b c, c b, c c$, "->"), 
		node((2,3), $0$, stroke:1pt),
	) #h(3em) #pause #pause
	#diagram(spacing:(0em,1.2em),
		node((1,0), $!(a b + a c)$), edge($a$, "->"), edge((2,1), $a$, "->"),
		node((0,1), $?b$), edge($e$, "->"),
		node((0,2), $b | b$), edge($b b$, "->"),
		node((0,3), $0 | 0$, stroke:1pt),
		node((2,1), $?c$), edge($e$, "->"),
		node((2,2), $c | c$), edge($c c$, "->"),
		node((2,3), $0 | 0$, stroke:1pt),
	) #pause
]
	#meanwhile
	#uncover("4-")[$tr !a(b+c) = { a b b, underline(a b c), underline(a c b), a c c }$] #uncover("6-")[$eq.not { a b b, a c c } = tr !(a b + a c)$]

---

=== Smoothness

#align(center)[#grid(columns:3,gutter:1.5em,
	onerule(
		name:$forall a$,
		$! t ->^a ? t'$,
		$t ->^a t'$
	),
	onerule(
		$? t ->^c t$,
		$t ->^c t'$
	),
	onerule(
		name:$forall a eq.not c$,
		$? t arrow.b$,
		$t ->^a t'$
	)
)
] #pause
#align(center)[
	#diagram(spacing:(0em,1.5em),
		node((1,0), $!a(b+c)$), edge($a$, "->"),
		node((1,1), $?(b+c)$), edge($c$, "->"),
		node((1,2), $b+c$), edge($b$, "->"), edge((2,3), $c$, "->"),
		node((0,3), $0$, stroke:1pt),
		node((2,3), $0$, stroke:1pt),
	) #h(3em) #pause #pause
	#diagram(spacing:(0em,1.5em),
		node((1,0), $!(a b + a c)$), edge($a$, "->"), edge((2,1), $a$, "->"),
		node((0,1), $?b$, stroke:1pt),
		node((2,1), $?c$), edge($c$, "->"),
		node((2,2), $c$), edge($c$, "->"),
		node((2,3), $0$, stroke:1pt),
	) #pause
]
	#meanwhile
	#uncover("3-")[$tr !a(b+c) = { underline(a c b), a c c }$] #uncover("5-")[$eq.not { underline(a), a c c } = tr !(a b + a c)$]

---

=== Affineness

- the proof need _deep smoothness_: rules on complex terms obtained by stacking rules of $cal(R)$ need to be smooth #pause

- without affineness, no deep smoothness:

#align(center)[#grid(columns:3,gutter:1.5em,
	onerule(
		name:$forall a$,
		$! t ->^a b.? t'$,
		$t ->^a t'$
	),
	onerule(
		$? t ->^c t'$,
		$t ->^c t'$
	),
	// onerule(
	// 	$? t ->^d ?t$,
	// 	$t arrow.b$
	// )
)
] #pause
#align(center)[
	#grid(columns: 7, gutter:1em,
		uncover("3-",onerule(
			$a. ? t ->^a ? t$ ,
			rule(
				$? t ->^c t'$,
				$t ->^c t' $
			)
		)),
		uncover("4-")[=],
		uncover("4-",prooftree(vertical-spacing:0.3em, stroke:(dash:"dashed"), rule(
			$a. ? t ->^a ? t$ ,
			$t ->^c t' $
		))),
		uncover("5-")[#h(1em)for smoothness, need],
		uncover("5-",prooftree(vertical-spacing:0.3em, stroke:(dash:"dashed"), rule(
			$a. ? t ->^a ? t$ ,
			$t ->^b t' $
		))),
		uncover("6-")[but],
		uncover("6-", onerule(
			$a. ? t arrow.not$ ,
			rule(
				$? t arrow.not$,
				$t ->^b t'$
			)
		)) ,
	)
]
 
#focus-slide[
	#emoji.radioactive #emoji.eighteen.not WARNING #emoji.eighteen.not #emoji.radioactive

	YOU ARE ABOUT TO ENTER THE MONAD ZONE

	COME IN AT YOUR PERIL

	#[#set text(14pt)
	(please note that the following part of the talk is heavily populated by monads, (co)algebras, functors, natural transformations and akin, it is highly recommended to not be allergic to those if you wish to pursue your journey with us)]
]


= Abstraction

== Algebras and coalgebras

- $CC$ a category with products (eg. $"Set"$) #pause
- *syntax*: endofunctor $Sigma : CC -> CC$ #pause
	- $Sigma$-algebra $i: Sigma X -> X$ #pause
#example[
	$Sigma X = product.co_(sigma in cal(O)) X^("ar" sigma)$

	For $t ::= 0 | a.t | t + t | ! t$, $Sigma X = 1 + A times X + X^2 + X$
] #pause
- *behaviour*: endofunctor $H : CC -> CC$ #pause
	- $H$-coalgebra $k : X -> H X$ #pause
#example[
	$H X = cal(P)_"ne" (A times X + 1)$
]

== Abstract GSOS 

- set of rules $cal(R)$ $~~>$ a *natural transformation* $rho_X : Sigma (X times H X) -> H Sigma^* X$ #pause

#example[
	For the previous example without $!$ : $Sigma X = 1 + A times X + X^2$, 
	$ rho : 1 + A times (X times cal(P)(1 + A times X)) + (X times cal(P)(1 + A times X))^2 -> cal(P)(1 + A times Sigma^* X) $ #pause

	- $rho(*) = { * }$ #h(1fr) #pause #sym.bullet $rho((a, t, T)) = { (a,t) }$ #h(1fr)#pause

	- $rho( (t, T), (u, U) ) = { (a, t') | forall (a,t') in T } union uncover("6-", { (a, u') | forall (a, u') in U } union ) uncover("7-", { * | * in T } union {* | * in U } )$
	
	#meanwhile	
	#only("3", align(center, onerule($0 arrow.b$))) 
	#only("4", align(center, onerule(name:$forall a$, $a.t ->^a t$))) 
	#only("5", align(center)[
		#grid(columns:1, gutter: 3em,
			onerule(
				name:$forall a$,
				$t + u ->^a t'$,
				$t ->^a t'$
			)
		)
	])
	#only("6", align(center)[
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
	#only("7", align(center)[
		#grid(columns:4, gutter: 3em,
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
			),
			onerule(
				$t +u arrow.b$,
				$u arrow.b$
			)
		)
	])
]

== Kleisli trace semantics

- recall $H X = cal(P)_"ne" (1 + A times X)$ #pause $= T B X$ 
	- $T = cal(P)_"ne"$ *effectful* behaviour #uncover("3-")[$~>$ non empty powerset : non-determinism]
	- $B = 1 + A times X$ *pure* behaviour #pause $~>$ words : $Z = A^oo$ (final $B$-algebra) #pause

- $tr x in cal(P)(A^oo) = T Z$ #pause

- $T$ is a *monad* #pause

- *Kleisli category* of $T$ #pause 
 $ A in "Kl"(T) &<=> A in CC wide wide 
	A rel B in "Kl"(T) &<=> A -> T B in CC $ #pause

- $B : CC -> CC$ *extends* to $overline(B) : "Kl"(T) -> "Kl"(T)$ (distributive law $lambda^B : B T => T B$)

---
 
- $Z = A^oo$ is a $B$-coalgebra in $"Kl"(T)$ #pause
$ zeta : Z rel B Z "or" Z -> T B Z wide wide zeta(epsilon) = {*}, quad zeta (a.w) = {(a,w)} $ #pause


- for any $k : X rel B X$, $h : X rel Z$ is a $overline(B)$-coalgebra morphism if
#align(center, diagram(
	node((0,0), $X$), edge($k$, "-|->"), edge((0,1), $h$, "--|-->"),
	node((1,0), $B X$), edge((1,1), $overline(B)h$, "--|-->", label-side:left),
	node((0,1), $Z$), edge($zeta$, "-|->"),
	node((1,1), $B Z$)
)) #pause

- suppose $"Kl"(T)$ enriched with an *order on maps with maximums*, define $"tr"_k$ the *greatest $overline(B)$-coalgebra morphism*


== Trace-GSOS

- GSOS rule
#only("1")[$ rho : Sigma (X times H X) -> H Sigma^* X $]#only("2-")[$ rho : Sigma (X times T B X) ->  T B Sigma^* X $] #pause #pause
- *Trace*-GSOS rule
#only("-4")[$ rho : Sigma (X times B X) ->  T B Sigma^* X $] #only("5-")[$ rho : Sigma (X times B X) rel B Sigma^* X $]
#pause $~>$ only pure observations #pause #pause

- $B$ and $Sigma$ extend to $"Kl"(T)$ (and $Sigma^*$) but not $+$ #h(1em) #emoji.face.unhappy #pause

- *affineness*: ask $T$ to be an *affine monad*


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

== Abstract smoothness

- diagrammatical condition #pause

#grid(columns:(60%,40%),align:(left, center),
	diagram(spacing:(1em, 1.5em),
		node((0,0), $Sigma T(X times B X)$), edge($angle.l T pi_1, T pi_2 angle.r$, "->"),
			edge((0,1), $lambda$, "->"), edge((0,0), (0,-1), (2,-1), (2,0), $"mix"$, "-->"),
		node((1,0), $Sigma (T X times T B X)$), edge($"dst"$, "->"),
		node((2,0), $Sigma T (X times B X)$), edge((2,1), $lambda$, "->"),
		node((0,1), $T Sigma (X times B X)$), edge($T rho$, "->"),
		node((0,2), $T^2 B Sigma^* X$), edge($mu$, "->"),
		node((1,2), $T B Sigma^* X$),
		node((2,1), $T Sigma (X times B X)$), edge($T rho$, "->"),
		node((2,2), $T^2 B Sigma^* X$), edge((1,2), $mu$, "->")
	),
	[#pause $union.big { rho(sigma(xi_1 ... xi_n)) | xi_i in "mix" Xi_i } = union.big { rho(sigma(xi_1 ... xi_n)) | xi_i in Xi_i }$ \ where $Xi_i subset X times B X$]
)

== Sketch of the proof

- Recall congruence $forall sigma, (forall i, t_i tilde u_i) => sigma(t_1 ... t_n) tilde sigma(u_1...u_n)$ #pause

	Prove $"tr"(sigma(t_1...t_n)) = [|sigma|]("tr" t_1 ... "tr" t_n)$ #pause

#align(center, diagram(
	node((0,0), $Sigma^* X$), edge($i^*$, "-|->"), edge((0,1), $Sigma^* "tr"_k$, "-|->"), edge((1,1), label:"?", label-side:center, stroke:0pt),
	node((1,0), $X$), edge($k$, "-|->"), edge((1,1), $"tr"_k$, "-|->"), edge((2,1), label:emoji.checkmark, label-side:center, stroke:0pt),
	node((2,0), $B X$), edge((2,1), $B "tr"_k$, "-|->", label-side:left),
	node((0,1), $Sigma^* Z$), edge($g$, "-|->", label-side:right),
	node((1,1), $Z$), edge($zeta$, "-|->", label-side:right),
	node((2,1), $B Z$)
)) #pause
- define $[|-|]\/g$ : semantics of $Z$ ($B$-coalgebra) + induction + trace #pause
- $Sigma^* X rel B Sigma^* X$ (with $rho^*$) #pause and $Z rel B Z$ #pause
- show $overline(B)$-coalgebra morphisms: #pause
	- $"tr" compose i quad checkmark$ #pause
	- $g compose Sigma^*"tr"$ more complicated : naturality + smoothness + map of distributive law of $rho^*$ #pause
- *maximality ?*


== To sum up: the theorem

#theorem[
	Let $CC$ be a cartesian category,#pause $T$ be a strong *affine* monad _for effects_, #pause $B$ an endofunctor _for behaviour_ that extends to $"Kl"(T)$, #pause $Sigma$ a endofunctor _for syntax_ that extends to $"Kl"(T)$ with all free objects ($Sigma^* X$), #pause let $Z$ be the final $B$-algebra, suppose there is an infinitary trace situation, and #pause let $rho : Sigma (X times B X) -> T B Sigma^* X$ be a natural transformation _representing Trace-GSOS rules_ #pause such that $rho$ is *smooth* and is a map of distributive laws, #pause *and that is sublinear (?)* #pause then trace equivalence is a congruence. #pause (Hopefully !)
]

= Conclusion
---

- concrete proof #emoji.checkmark #pause
- abstract:
	- missing the "sublinearity" $~>$ using presheaves? #pause
	- moving to Eilenberg-Moore to have _finite, partial_ and trace semantics as a *final coalgebra* #pause
- thank you and bravo if you are still there ! #pause

#align(center)[
	#text(font:"z003", size: 42pt)[\~ The End#h(0.1em)#footnote[#uncover("5-")[for today...]] \~]
]

#align(right)[
	#text(fill:gray, size:14pt)[Powered by #link("https://typst.app/")[Typst]]
]