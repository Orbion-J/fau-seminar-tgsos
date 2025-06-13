#import "@preview/touying:0.6.1": *
#import themes.metropolis: *
#import "@preview/curryst:0.5.0": rule, prooftree
#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge
#import "@preview/great-theorems:0.1.2" : *
#import "@preview/datify:0.1.4": custom-date-format

#show list.item: it => {
//   // The generated terms is not tight
//   // So setting `par.spacing` is to set the result lists' spacing
//   let spacing = if list.spacing != auto {
//     enum.spacing
//   } else if enum.tight {
//     par.leading
//   } else {
//     par.spacing
//   }
//   set par(spacing: spacing)

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
  footer: self => [#self.info.title -- Jourde et al.],
  config-info(
    title: [(Abstract) GSOS for Trace Equivalence],
    subtitle: [CAlCO 2025 -- Glasgow],
    author: [*Robin Jourde*#footnote[ENS de Lyon, Université Savoie Mont Blanc], Pouya Partow#footnote[University of Birmingham]<uob>, Jonas Forster#footnote[*Friedrich-Alexander-Universität Erlangen-Nürnberg*]<fau>, under the supervision of Stelios Tsampas#footnote[Syddansk Universitet], Sergey Goncharov@uob, Henning Urbat@fau],
    date: custom-date-format(datetime(year:2025, month:6,day:16),"DD Month YYYY"),
    // institution: [],
    // logo: [],
  ),
  config-common(
		// handout: true,
	)
)

#show footnote.entry: set text(size:15pt)
#set footnote(numbering:"*")
#set footnote.entry(separator: none)

#set heading(numbering: "1.1")

#show outline.entry: it => it.indented(it.prefix(), it.body())
// #show outline.entry.where(level : 2) : set text(size: 10pt)

// Theorem config by great-theorem
#show: great-theorems-init
#let theorem = mathblock(
	blocktitle: "Theorem",
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

#let cat(catname) = [#set math.text(weight:"bold"); #math.sans(catname)]
#let CSLat = cat("CSLat")
#let Set = cat("Set")


#title-slide()

= Outline <touying:hidden>

#outline(title: none, indent: 2em, depth: 2)


= (Abstract) GSOS

== GSOS 

- a *framework* for specifying reduction rules and semantics #pause
	$->$ rule format #pause

- *syntax* #pause :
	Set of operations $cal(O)$ with arity map $"ar" : cal(O) -> NN$ #pause

#only("5",example[
	$cal(O) = {0^0, a.^1, +^2, f^1} ⇒ t ::= 0 | a.t quad forall a in L | t + t | f(t)$

	Eg. for $a,b,c in A$ : $a.(b.a.0+ f(a.c.0)) = a(b a+ f(a c))$
]) #pause

- *behaviour* (LTS) #pause :
  $x ->^a x' $
	($a ∈ L$ for some fixed set $L$) 
  #pause

- *GSOS rules*

#only("6-",align(center, onerule(
			$sigma(x_1 ... x_n) ->^c u$,
			${ x_i ->^(a) y_(i,a,j) }_(1 ≤ i ≤ n, a ∈ A_i, 1 ≤ j ≤ m_(i a))$,
			${ x_i ↛^b }_(1 ≤ i ≤ n, b ∈ B_i)$,
	)))

with $sigma in cal(O), n = "ar" sigma, A_i, B_i ⊆ L$ disjoint, $u$ a term with variables in ${ x_i ..., y_(i,a,j)...}$ #pause

- set of GSOS rules $⇒$ behaviour of terms

---

#example[

#align(center)[
	#grid(columns:3, gutter: 2em,
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
	)
] 
#pause
\  

#align(center)[ 
	 #diagram(spacing:(0.5em,1.5em),
		node((1, 0), [$a(b+c)$]), edge($a$, "->"),
		node((1, 1), [$b+c$]), edge($b$, "->"), edge((2,2), $c$, "->"),
		node((0, 2), [$0$]),
		node((2, 2), [$0$])
	) #pause #h(3em) 
	#diagram(spacing:(0.5em, 1.5em),
		node((1, 0), [$a b+a c$]), edge($a$, "->"), edge((2,1), $a$, "->"),
		node((0, 1), [$b$]), edge($b$, "->"),
		node((0, 2), [$0$]),
		node((2, 1), [$c$]), edge($c$, "->"),
		node((2, 2), [$0$])
	))
]
]

== *Abstract* GSOS

- syntax functor $Sigma$ and behaviour functor $H$ #pause

  #only("1-4",[
    $t ::= 0 | a.t quad forall a in L | t + t quad ~~> quad Sigma X = 1 + A times X + X^2$
    
    $x ->^a x' quad ~~> quad x' ∈ k(x)(a)$ with $k : X -> H X = cal(P)(X)^L$
  ])

- rules $~~>$ a *natural transformation* $rho_X : Sigma (X times H X) -> H Sigma^* X$ #pause

#example[
	$ rho : 1 + A times (X × cal(P)(X)^L) + (X times cal(P)(X)^L)^2 -> cal(P)(Sigma^* X)^L $ #pause

	- $rho(*)(c) = ∅ $ #pause

	- $rho((a', t, T))(a) = { t } "if" a = a' "and" ∅ "otherwise"$
	#only("5", align(center, onerule(name:$forall a$, $a.t ->^a t$))) #pause

	- $rho( (t, T), (u, U) )(a) = { t' | t' in T(a) } union uncover("7-", { u' | u' in U(a) } ) $
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

]

= Trace equivalence

== Program equivalence

- many different notions (linear-time branching-time spectrum): bisimilarity, trace equivalence#pause

- important property: *congruence*
	$ (forall i, x_i tilde y_i) => sigma(x_1 .. x_n) tilde sigma(y_1 ... y_n) $#pause

#theorem(title:[D. Turi and G. Plotkin, 1997])[
  #set align(center)
  GSOS $=>$ bisimilarity is a congruence
] #pause

- what about trace equivalence?

== Trace and trace equivalence

- different flavors: partial vs. complete, finite vs. infinite #pause
- partial finite traces
	$ "tr"(x) = union.big_(n in NN) { w in L^n mid(|) x ->^(w_1) x_1 ->^(w_2) ... ->^(w_n) x_n } $#pause
- $"tr"(x) ∈ frak(T) := { A ⊆ L^* | ε ∈ A ∧ A "prefix-closed" }$ #pause
#remark[
	$"tr"$ is the unique map such $X -> frak(T)$ such that $a.w ∈ "tr"(x) ⇔ x→^a y ∧ w ∈ "tr"(y)$ ("_coalgebra morphism_")
]#pause
- trace equivalence: $x tilde_"tr" y <=> "tr"(x) = "tr"(y)$

---
	$ "tr"(x) = union.big_(n in NN) { w in L^n mid(|) x ->^(w_1) x_1 ->^(w_2) ... ->^(w_n) x_n } $

#example[
	$"tr" a(b+c) = pause { ε, a, a b, a c }$, #pause $"tr" (a b + a c) = pause { ε, a, a b, a c}$, #pause $"tr" x = pause { ε, a, a b, a b b, a b b b, ...} $
	#meanwhile
	#align(center)[
		#uncover("1-",diagram(spacing:(0.5em,1.5em),
			node((1, 0), [$a(b+c)$]), edge($a$, "->"),
			node((1, 1), [$b+c$]), edge($b$, "->"), edge((2,2), $c$, "->"),
			node((0, 2), [$0$]),
			node((2, 2), [$0$])
		)) #h(1em) #box(uncover("4")[$tilde_"tr"$], height:7em) #h(1em)
		#uncover("3-", diagram(spacing:(0.5em, 1.5em),
			node((1, 0), [$a b+a c$]), edge($a$, "->"), edge((2,1), $a$, "->"),
			node((0, 1), [$b$]), edge($b$, "->"),
			node((0, 2), [$0$]),
			node((2, 1), [$c$]), edge($c$, "->"),
			node((2, 2), [$0$])
		))	
		#only("5-")[#h(3em) #diagram(spacing:(1em, 1.5em),
			node((0, 0), [$x$]), edge($a$, "->"),
			node((0, 1), [$y$]), edge((0,1), $b$, "->", bend:-130deg),
		)]
	]
] 

== De Simone Format 

- De Simone rule format (R. de Simone, 1985): #pause

	#grid(columns:(3fr,2fr), [
	- positive (no negative premise)
	- at most one positive premise per variable
	- linearity: each variable at most once in $u$ + no $x_i$ for $i ∈ I$ in $u$ 
	],[
	#align(center, onerule(
		$sigma(x_1 ... x_n) ->^c u$,
		${ x_i ->^(a_i) y_i }_(i ∈ I)$,
	))
	])
	#pause

#theorem(title:[B. Bloom, 1994, restricted to GSOS])[
  #set align(center)
  De Simone $⇒$ trace equivalence is a congruence
]

- abstract? #pause


#remark(title:[B. Klin, 2005 and 2009])[
  test suites and logical distributive laws
]

== Abstract Trace Semantics

- recall behaviour $k : X -> H X = cal(P)(X)^L ≅ (cal(P)_"ne" (X)+1)^L$ #pause
	- $T = cal(P)_"ne"$: *effectful* behaviour (non-determinism)
	- $B = (-+1)^L$: *pure* behaviour (labels and termination) #pause

- $ν B = frak(T)$ set of (partial finite) traces: final $B$-coalgebra #pause

- categories of algebras (Eilenberg-Moore) $Set^T = CSLat$ category of unbounded complete semi-lattices #pause

- $B$ lifts (with $δ^B : T B → B T$) and $nu overline(B) = nu B$ #pause

---

- abstract GSOS theory in $CSLat$:
$ overline(ρ) : overline(Σ)(X × overline(B) X) → overline(B)(overline(Σ)^* X) $ #pause

- universal semantics $τ : μ overline(Σ) → ν overline(B)$
#align(center)[
#diagram(
	node((0,0), $overline(Σ)μ overline(Σ)$), edge("->"), edge((0,1), "-->", $overline(Σ)τ$), 
	node((1,0), $μ overline(Σ)$), edge("->"), edge((1,1), "-->", $τ$, right),
	node((2,0), $overline(B)μ overline(Σ)$), edge((2,1),"-->", $overline(B)τ$),
	node((0,1), $overline(Σ)ν overline(B)$), edge("->"),
	node((1,1), $ν overline(B)$), edge("->"),
	node((2,1), $overline(B)ν overline(B)$), 
)] #pause

- define $"tr" : μ Σ →^ξ μ overline(Σ) →^τ ν B$ #pause

- left square $⇒$ $"tr"$ is a congruence #emoji.face #pause

- how to get $overline(ρ)$ natural transformation in $CSLat$?

== Trace-GSOS

- rule format 
#align(center, onerule(
      $sigma(x_1 ... x_n) ->^c u$,
      ${ x_i ->^(a) y_i }_(a ∈ A_i)$,
	  ${ x_i ↛^b }_(b ∈ B_i)$
  ))
  #pause 

#remark[Only *pure* observations/premises: observe each variable at each label *once and only once* ]
#pause

- natural transformation
#only("1-3")[$ ρ : Σ(X × H X) → H Σ^* X $]
#only("4")[$ ρ : Σ(X × B T X) → B T Σ^* X $]
#only("5-")[$ ρ : Σ(X × B X) → B T Σ^* X $]

#pause #pause #pause
- De Simone rules $→$ Trace-GSOS rules:
$ cal(S)(r) = { r' "Trace-GSOS rule" | ∀ i ∈ I^r, a_i^r ∈ A_i^r' } $ 

---

- characterize "good" Trace-GSOS specifications: smooth and minimally linear#pause

#theorem[
	"good" Trace-GSOS specifications $⟺$ De Simone specifications
]
#pause
#theorem[
	"good" Trace-GSOS specifications $⟹$ $ρ$ yields a natural transformation $overline(ρ)$ in $CSLat$
]
#pause

- #emoji.construction find an easy/better abstract characterization of "good" Trace-GSOS

= Conclusion...
---

- Eilenberg-Moore trace semantics #pause

- abstract GSOS in Eilenberg-Moore category  #pause

- works for LTSs  #pause

- #emoji.construction easier to check abstract condition  #pause

- #emoji.construction other monads: probabilistic distributions #pause

- #emoji.construction adequacy of operational models #pause

#align(center)[
	#text(font:"z003", size: 42pt, fill:gray)[\~ Thank you for your attention \~]
]

// #example[
// 	#align(center)[
// 		#grid(columns:5, gutter: 1.5em,
// 			[#onerule(
// 				$? t ->^a t + t'$,
// 				$t ->^a t'$,
// 				$t ->^a t''$,
// 			) #emoji.face.unhappy],	
// 			[#onerule(
// 				$! t ->^a t + t$,
// 				$t ->^a t'$,
// 			) #emoji.face.unhappy],
// 			[#onerule(name:$forall a$, $a.t ->^a t$) #emoji.face.unhappy],
// 			[#onerule(
// 				name:$forall a, b$,
// 				$a.t ->^a t$,
// 				$t ->^b t'$
// 			) #emoji.face.cool],
// 			[#onerule(
// 				name:$forall a$,
// 				$a.t ->^a t$,
// 				$ t arrow.b$
// 			) #emoji.face.cool]
// 		)
// 	]
// ]#pause
// #v(-0.5em)
// - require 2 extra conditions on the set of rules: #pause
// 	- *affineness*: for each term, there is a least one rule that can apply #pause $~> k : X -> only("-4",cal(P)) #only("5-")[$cal(P)_"ne"$] (A times X + {star})$ #pause #pause
// 	- *smoothness*: $x_i$ in the target, the observation on $x_i$ is *irrelevant* ie. any other observation could have been done (the same rule for each other possible observation exists)

// == Theorem 

// #theorem[
// 	Let $cal(R)$ be a smooth and affine set of Trace-GSOS rules. Let $X$ be a set of terms equipped with behaviour $k : X -> cal(P)_"ne" (A times X + {star})$ induced by $cal(R)$. Then trace equivalence $tilde_"tr"$ is a congruence.
// ]#pause
// #proof[
// 	Show that the trace of a complex term can be obtained from the traces of its subterms.#pause
// 	- consider complex terms with words of $A^oo$ as leaves, and behaviour induced by $cal(R)$ with $a.w ->^a w$ and $epsilon arrow.b$ #pause
// 	- extend the trace function of this system to maps $[|u|] : (cal(P)_"ne" A^oo)^n → cal(P)_"ne" A^oo$ for each complex term $u$ with $n$ free variables #pause
// 	- prove $"tr" u[t_1 ... t_n] = [|u|]("tr" t_1 ... "tr" t_n)$ by showing that both sides are maximal coalgebra morphisms
// ]

// == Counter-examples

// Affineness, smoothness and sublinearity are *necessary* #pause

// === Sublinearity 

// #align(center)[#grid(columns:2,gutter:1.5em,
// 	onerule(
// 		name:$forall a$,
// 		$! t ->^a ? t'$,
// 		$t ->^a t'$
// 	),
// 	onerule(
// 		name:$forall a$
// 		,
// 		$? t ->^e t | t$,
// 		$t ->^a t'$
// 	),
// )
// ] #pause
// #align(center)[
// 	#diagram(spacing:(0em,1.2em),
// 		node((2,0), $!a(b+c)$), edge($a$, "->"),
// 		node((2,1), $?(b+c)$), edge($e$, "->"),
// 		node((2,2), $(b+c)|(b+c)$), edge($b b, b c, c b, c c$, "->"), 
// 		node((2,3), $0$),
// 	) #h(3em) #pause #pause
// 	#diagram(spacing:(0em,1.2em),
// 		node((1,0), $!(a b + a c)$), edge($a$, "->"), edge((2,1), $a$, "->"),
// 		node((0,1), $?b$), edge($e$, "->"),
// 		node((0,2), $b | b$), edge($b b$, "->"),
// 		node((0,3), $0 | 0$),
// 		node((2,1), $?c$), edge($e$, "->"),
// 		node((2,2), $c | c$), edge($c c$, "->"),
// 		node((2,3), $0 | 0$),
// 	) #pause
// ]
// 	#meanwhile
// 	#uncover("4-")[$tr !a(b+c) = { a b b, underline(a b c), underline(a c b), a c c }$] #uncover("6-")[$eq.not { a b b, a c c } = tr !(a b + a c)$]

// ---

// === Smoothness

// #align(center)[#grid(columns:3,gutter:1.5em,
// 	onerule(
// 		name:$forall a$,
// 		$! t ->^a ? t'$,
// 		$t ->^a t'$
// 	),
// 	onerule(
// 		$? t ->^c t$,
// 		$t ->^c t'$
// 	),
// 	onerule(
// 		name:$forall a eq.not c$,
// 		$? t arrow.b$,
// 		$t ->^a t'$
// 	)
// )
// ] #pause
// #align(center)[
// 	#diagram(spacing:(0em,1.5em),
// 		node((1,0), $!a(b+c)$), edge($a$, "->"),
// 		node((1,1), $?(b+c)$), edge($c$, "->"),
// 		node((1,2), $b+c$), edge($b$, "->"), edge((2,3), $c$, "->"),
// 		node((0,3), $0$),
// 		node((2,3), $0$),
// 	) #h(3em) #pause #pause
// 	#diagram(spacing:(0em,1.5em),
// 		node((1,0), $!(a b + a c)$), edge($a$, "->"), edge((2,1), $a$, "->"),
// 		node((0,1), $?b$),
// 		node((2,1), $?c$), edge($c$, "->"),
// 		node((2,2), $c$), edge($c$, "->"),
// 		node((2,3), $0$),
// 	) #pause
// ]
// 	#meanwhile
// 	#uncover("3-")[$tr !a(b+c) = { underline(a c b), a c c }$] #uncover("5-")[$eq.not { underline(a), a c c } = tr !(a b + a c)$]

// ---

// === Affineness

// - the proof need _deep smoothness_: rules on complex terms obtained by stacking rules of $cal(R)$ need to be smooth #pause

// - without affineness, no deep smoothness:

// #align(center)[#grid(columns:3,gutter:1.5em,
// 	onerule(
// 		name:$forall a$,
// 		$! t ->^a b.? t'$,
// 		$t ->^a t'$
// 	),
// 	onerule(
// 		$? t ->^c t'$,
// 		$t ->^c t'$
// 	),
// 	// onerule(
// 	// 	$? t ->^d ?t$,
// 	// 	$t arrow.b$
// 	// )
// )
// ] #pause
// #align(center)[
// 	#grid(columns: 7, gutter:1em,
// 		uncover("3-",onerule(
// 			$a. ? t ->^a ? t$ ,
// 			rule(
// 				$? t ->^c t'$,
// 				$t ->^c t' $
// 			)
// 		)),
// 		uncover("4-")[=],
// 		uncover("4-",prooftree(vertical-spacing:0.3em, stroke:(dash:"dashed"), rule(
// 			$a. ? t ->^a ? t$ ,
// 			$t ->^c t' $
// 		))),
// 		uncover("5-")[#h(1em)for smoothness, need],
// 		uncover("5-",prooftree(vertical-spacing:0.3em, stroke:(dash:"dashed"), rule(
// 			$a. ? t ->^a ? t$ ,
// 			$t ->^b t' $
// 		))),
// 		uncover("6-")[but],
// 		uncover("6-", onerule(
// 			$a. ? t arrow.not$ ,
// 			rule(
// 				$? t arrow.not$,
// 				$t ->^b t'$
// 			)
// 		)) ,
// 	)
// ]
 
// #focus-slide[
// 	#emoji.radioactive #emoji.eighteen.not WARNING #emoji.eighteen.not #emoji.radioactive

// 	YOU ARE ABOUT TO ENTER THE MONAD ZONE

// 	COME IN AT YOUR PERIL

// 	#[#set text(14pt)
// 	(please note that the following part of the talk is heavily populated by monads, (co)algebras, functors, natural transformations and akin, it is highly recommended to not be allergic to those if you wish to pursue your journey with us)]
// ]


// = Abstraction

// == Algebras and coalgebras

// - $CC$ a category with products (eg. $"Set"$) #pause
// - *syntax*: endofunctor $Sigma : CC -> CC$ #pause
// 	- $Sigma$-algebra $i: Sigma X -> X$ #pause
// #example[
// 	$Sigma X = product.co_(sigma in cal(O)) X^("ar" sigma)$

// 	For $t ::= 0 | a.t | t + t | ! t$, $Sigma X = 1 + A times X + X^2 + X$
// ] #pause
// - *behaviour*: endofunctor $H : CC -> CC$ #pause
// 	- $H$-coalgebra $k : X -> H X$ #pause
// #example[
// 	$H X = cal(P)_"ne" (A times X + 1)$
// ]

// == Abstract GSOS 

// - set of rules $cal(R)$ $~~>$ a *natural transformation* $rho_X : Sigma (X times H X) -> H Sigma^* X$ #pause

// #example[
// 	For the previous example without $!$ : $Sigma X = 1 + A times X + X^2$, 
// 	$ rho : 1 + A times (X times cal(P)(1 + A times X)) + (X times cal(P)(1 + A times X))^2 -> cal(P)(1 + A times Sigma^* X) $ #pause

// 	- $rho(*) = { * }$ #h(1fr) #pause #sym.bullet $rho((a, t, T)) = { (a,t) }$ #h(1fr)#pause

// 	- $rho( (t, T), (u, U) ) = { (a, t') | forall (a,t') in T } union uncover("6-", { (a, u') | forall (a, u') in U } union ) uncover("7-", { * | * in T } union {* | * in U } )$
	
// 	#meanwhile	
// 	#only("3", align(center, onerule($0 arrow.b$))) 
// 	#only("4", align(center, onerule(name:$forall a$, $a.t ->^a t$))) 
// 	#only("5", align(center)[
// 		#grid(columns:1, gutter: 3em,
// 			onerule(
// 				name:$forall a$,
// 				$t + u ->^a t'$,
// 				$t ->^a t'$
// 			)
// 		)
// 	])
// 	#only("6", align(center)[
// 		#grid(columns:2, gutter: 3em,
// 			onerule(
// 				name:$forall a$,
// 				$t + u ->^a t'$,
// 				$t ->^a t'$
// 			),
// 			onerule(
// 				name:$forall a$,
// 				$t + u ->^a u'$,
// 				$u ->^a u'$
// 			)
// 		)
// 	])
// 	#only("7", align(center)[
// 		#grid(columns:4, gutter: 3em,
// 			onerule(
// 				name:$forall a$,
// 				$t + u ->^a t'$,
// 				$t ->^a t'$
// 			),
// 			onerule(
// 				name:$forall a$,
// 				$t + u ->^a u'$,
// 				$u ->^a u'$
// 			),
// 			onerule(
// 				$t +u arrow.b$,
// 				$t arrow.b$,
// 			),
// 			onerule(
// 				$t +u arrow.b$,
// 				$u arrow.b$
// 			)
// 		)
// 	])
// ]

// == Kleisli trace semantics

// - recall $H X = cal(P)_"ne" (1 + A times X)$ #pause $= T B X$ 
// 	- $T = cal(P)_"ne"$ *effectful* behaviour #uncover("3-")[$~>$ non empty powerset : non-determinism]
// 	- $B = 1 + A times X$ *pure* behaviour #pause $~>$ words : $Z = A^oo$ (final $B$-algebra) #pause

// - $tr x in cal(P)(A^oo) = T Z$ #pause

// - $T$ is a *monad* #pause

// - *Kleisli category* of $T$ #pause 
//  $ A in "Kl"(T) &<=> A in CC wide wide 
// 	A rel B in "Kl"(T) &<=> A -> T B in CC $ #pause

// - $B : CC -> CC$ *extends* to $overline(B) : "Kl"(T) -> "Kl"(T)$ (distributive law $lambda^B : B T => T B$)

// ---
 
// - $Z = A^oo$ is a $B$-coalgebra in $"Kl"(T)$ #pause
// $ zeta : Z rel B Z "or" Z -> T B Z wide wide zeta(epsilon) = {*}, quad zeta (a.w) = {(a,w)} $ #pause


// - for any $k : X rel B X$, $h : X rel Z$ is a $overline(B)$-coalgebra morphism if
// #align(center, diagram(
// 	node((0,0), $X$), edge($k$, "-|->"), edge((0,1), $h$, "--|-->"),
// 	node((1,0), $B X$), edge((1,1), $overline(B)h$, "--|-->", label-side:left),
// 	node((0,1), $Z$), edge($zeta$, "-|->"),
// 	node((1,1), $B Z$)
// )) #pause

// - suppose $"Kl"(T)$ enriched with an *order on maps with maximums*, define $"tr"_k$ the *greatest $overline(B)$-coalgebra morphism*


// == Trace-GSOS

// - GSOS rule
// #only("1")[$ rho : Sigma (X times H X) -> H Sigma^* X $]#only("2-")[$ rho : Sigma (X times T B X) ->  T B Sigma^* X $] #pause #pause
// - *Trace*-GSOS rule
// #only("-4")[$ rho : Sigma (X times B X) ->  T B Sigma^* X $] #only("5-")[$ rho : Sigma (X times B X) rel B Sigma^* X $]
// #pause $~>$ only pure observations #pause #pause

// - $B$ and $Sigma$ extend to $"Kl"(T)$ (and $Sigma^*$) but not $+$ #h(1em) #emoji.face.unhappy #pause

// - *affineness*: ask $T$ to be an *affine monad*


// == Strong and affine monads

// - *strong monad*: $"st"_(X,Y) : X times T Y -> T(X times Y)$ #pause $~~>$ $"st"' : T X times Y -> T(X times Y)$ #pause

// - double strength $"dst" : T X times T Y ->^("st") T (T X times Y) ->^(T "st"') T^2 (X times Y) ->^mu T ( X times Y)$ #pause (and $"dst"'$) #pause

// - *affine monad*: $T X times T Y ->^"dst" T (X times Y) -->^(angle.l T pi_1, T pi_2 angle.r) T X times T Y = "id"$ or $eta_1 : 1 ->^tilde.eq T 1 $ #pause

// - *affine part*: greatest affine submonad #pause

// #example[
// 	- Powerset $cal(P) ~~> cal(P)_"ne"$ #pause
// 	- (Sub)distribution $cal(S) ~~> cal(D)$ #pause
// 		with $cal(D)X = { sum_(i in I) p_i x_i | sum p_i = 1, x_i in X, I "finite"}$ and $cal(S)X = { sum_(i in I) p_i x_i | sum p_i <= 1, x_i in X, I "finite" }$ #pause
// 	- Maybe $- + 1 ~~> "Id"$
// ]

// == Abstract smoothness

// - diagrammatical condition #pause

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
// 	[#pause $union.big { rho(sigma(xi_1 ... xi_n)) | xi_i in "mix" Xi_i } = union.big { rho(sigma(xi_1 ... xi_n)) | xi_i in Xi_i }$ \ where $Xi_i subset X times B X$]
// )

// == Sketch of the proof

// - Recall congruence $forall sigma, (forall i, t_i tilde u_i) => sigma(t_1 ... t_n) tilde sigma(u_1...u_n)$ #pause

// 	Prove $"tr"(sigma(t_1...t_n)) = [|sigma|]("tr" t_1 ... "tr" t_n)$ #pause

// #align(center, diagram(
// 	node((0,0), $Sigma^* X$), edge($i^*$, "-|->"), edge((0,1), $Sigma^* "tr"_k$, "-|->"), edge((1,1), label:"?", label-side:center, stroke:0pt),
// 	node((1,0), $X$), edge($k$, "-|->"), edge((1,1), $"tr"_k$, "-|->"), edge((2,1), label:emoji.checkmark, label-side:center, stroke:0pt),
// 	node((2,0), $B X$), edge((2,1), $B "tr"_k$, "-|->", label-side:left),
// 	node((0,1), $Sigma^* Z$), edge($g$, "-|->", label-side:right),
// 	node((1,1), $Z$), edge($zeta$, "-|->", label-side:right),
// 	node((2,1), $B Z$)
// )) #pause
// - define $[|-|]\/g$ : semantics of $Z$ ($B$-coalgebra) + induction + trace #pause
// - $Sigma^* X rel B Sigma^* X$ (with $rho^*$) #pause and $Z rel B Z$ #pause
// - show $overline(B)$-coalgebra morphisms: #pause
// 	- $"tr" compose i quad checkmark$ #pause
// 	- $g compose Sigma^*"tr"$ more complicated : naturality + smoothness + map of distributive law of $rho^*$ #pause
// - *maximality ?*


// == To sum up: the theorem

// #theorem[
// 	Let $CC$ be a cartesian category,#pause $T$ be a strong *affine* monad _for effects_, #pause $B$ an endofunctor _for behaviour_ that extends to $"Kl"(T)$, #pause $Sigma$ a endofunctor _for syntax_ that extends to $"Kl"(T)$ with all free objects ($Sigma^* X$), #pause let $Z$ be the final $B$-algebra, suppose there is an infinitary trace situation, and #pause let $rho : Sigma (X times B X) -> T B Sigma^* X$ be a natural transformation _representing Trace-GSOS rules_ #pause such that $rho$ is *smooth* and is a map of distributive laws, #pause *and that is sublinear (?)* #pause then trace equivalence is a congruence. #pause (Hopefully !)
// ]

// = Conclusion
// ---

// - concrete proof #emoji.checkmark #pause
// - abstract:
// 	- missing the "sublinearity" $~>$ using presheaves? #pause
// 	- moving to Eilenberg-Moore to have _finite, partial_ and trace semantics as a *final coalgebra* #pause
// - thank you and bravo if you are still there ! #pause

// #align(center)[
// 	#text(font:"z003", size: 42pt)[\~ The End#h(0.1em)#footnote[#uncover("5-")[for today...]] \~]
// ]

// #align(right)[
// 	#text(fill:gray, size:14pt)[Powered by #link("https://typst.app/")[Typst]]
// ]