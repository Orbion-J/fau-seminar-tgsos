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
    title: [(Abstract) GSOS for Trace Equivalence -- Early Ideas],
    subtitle: [CALCO 2025 -- Glasgow],
    author: [*Robin Jourde*#footnote[ENS de Lyon, Université Savoie Mont Blanc], Pouya Partow#footnote[University of Birmingham]<uob>, Jonas Forster#footnote[*Friedrich-Alexander-Universität Erlangen-Nürnberg*]<fau>, in collaboration with Stelios Tsampas#footnote[Syddansk Universitet], Sergey Goncharov@uob, Henning Urbat@fau],
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

// = Outline <touying:hidden>

// #outline(title: none, indent: 2em, depth: 2)


= (Abstract) GSOS

== GSOS 

- a *framework* for specifying reduction rules and semantics of systems
	$->$ rule format #pause

- *syntax*: 
	operations with arities #pause
	// Set of operations $cal(O)$ with arity map $"ar" : cal(O) -> NN$ #pause

// #only("3",example[
// 	$cal(O) = {0 slash 0, a. slash 1, + slash 2, f slash 1} ~~> t ::= 0 | a.t quad forall a in L | t + t | f(t)$

// 	Eg. for $a,b,c in A$ : $a.(b.a.0+ f(a.c.0)) = a(b a+ f(a c))$
// ]) #pause

- *behaviour* (LTS):
  $x ->^a x' $
	($a ∈ L$ for some fixed set $L$) 
  #pause

- *GSOS rules*

// #only("4-",align(center, onerule(
// 			$sigma(x_1 ... x_n) ->^c u$,
// 			${ x_i ->^(a) y_(i,a,j) }_(1 ≤ i ≤ n, a ∈ A_i, 1 ≤ j ≤ m_(i a))$,
// 			${ x_i ↛^b }_(1 ≤ i ≤ n, b ∈ B_i)$,
// 	)))

// with $sigma in cal(O), n = "ar" sigma, A_i, B_i ⊆ L$ disjoint, $u$ a term with variables in ${ x_i ..., y_(i,a,j)...}$ #pause

#align(center, onerule(
	$σ(x_1 ... x_n) ->^c u$,
	$x_1 ->^(a_1) y_1$,
	$...$,
	$x_1 ->^(a_1) y_k$,
	$x_1 ->^(a_2) y_(k+1)$,
	$...$,
	$thin$,
	$x_2 ->^(a_1) y_l$,
	$...$,
	$quad$,
	$x_1 ↛^(b_1)$,
	$...$
))

	// #show: it => list(it, marker:hide(sym.bullet))
#list(marker:(hide(sym.bullet)))[ 
	#set list(marker:  sym.triangle.filled.small.r)
	- $x_i, y_j$ distinct *variables*
	- $u$ term with variables $x_i, y_j$
] #pause

- set of GSOS rules $⇒$ behaviour of terms

---

#example[

$ t ::= 0 | a.t quad forall a in L | t + t $

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
	)
]
]

== Abstract GSOS

- syntax functor $Sigma$ and behaviour functor $H$ (on a category $ℂ$) #pause

  #only("1-4",[
    $t ::= 0 | a.t quad forall a in L | t + t quad ~~> quad Sigma X = 1 + A times X + X^2$
    
    $x ->^a x' quad ~~> quad x' ∈ k(x)(a)$ with $k : X -> H X = cal(P)(X)^L$
  ])

- rules $~~>$ a *natural transformation* $rho_X : Sigma (X times H X) -> H Sigma^star X$ #pause

#example[
	$ rho : 1 + A times (X × cal(P)(X)^L) + (X times cal(P)(X)^L)^2 -> cal(P)(Sigma^star X)^L $ #pause

	- $rho(*)(a) = ∅ $ #pause

	- $rho((a', t, T))(a) = { t } "if" a = a' "and" ∅ "otherwise"$
	#only("5", align(center, onerule(name:$forall a$, $a.t ->^a t$))) #pause

	- $rho( (t, T), (u, U) )(a) = { t' | t' in T(a) } union { u' | u' in U(a) } = T union U$
	#only("6-", align(center)[
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

- many different notions (linear-time branching-time spectrum), eg. bisimilarity, trace equivalence#pause

- important property: *congruence*
	$ forall σ ∈ cal(O), (forall i, x_i tilde y_i) => sigma(x_1 .. x_n) tilde sigma(y_1 ... y_n) $#pause

#theorem(title:[D. Turi and G. Plotkin, 1997])[
  #set align(center)
  abstract GSOS $=>$ bisimilarity is a congruence
] #pause

- what about trace equivalence?

== Trace and trace equivalence

// - different flavors: partial vs. complete, finite vs. infinite #pause
- partial finite traces
	$ "tr"(x) = union.big_(n in NN) { w in L^n mid(|) x ->^(w_1) x_1 ->^(w_2) ... ->^(w_n) x_n } $#pause
- $"tr"(x) ∈ frak(T) := { A ⊆ L^star | ε ∈ A ∧ A "prefix-closed" }$ #pause
#remark[
	$"tr"$ is the unique map $X -> frak(T)$ such that $a.w ∈ "tr"(x) ⇔ x→^a y ∧ w ∈ "tr"(y)$ ("_coalgebra morphism_")
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
	- no negative premise
	- at most one premise per variable
	- linearity: each variable at most once in $u$ + no $x_i$ such that $x_i ->^(a_i) y_i$ in $u$ 
	],[
	// #align(center, onerule(
	// 	$sigma(x_1 ... x_n) ->^c u$,
	// 	${ x_i ->^(a_i) y_i }_(i ∈ I)$,
	// ))
	#align(center, onerule(
		$sigma(x_1 ... x_n) ->^c u$,
		$x_i ->^(a_i) y_i$,
		$...$,
		$x_j ->^(a_j) y_j$

	))
	])
	#pause

#theorem(title:[B. Bloom, 1994, restricted to GSOS])[
  #set align(center)
  De Simone $⇒$ trace equivalence is a congruence
]

---
#example(title:"With negative premises")[
	#set align(center)
	#grid(columns: 5,
		$... +$,
		h(2em),
		onerule(
			name:$forall a$,
			$f(x) ->^a g(y)$,
			$x ->^a y$
		),
		h(3em),
		onerule(
			$g(x) ->^b x$,
			$x ↛^b$	
		)
	)
	#pause	
		#diagram(spacing:(0.5em,1.5em),
			node((1, 0), [$f(a(b+c))$]), edge($a$, "->"),
			node((1, 1), [$g(b+c)$]), edge("-/->"), 
			node((1, 2))
		) #h(3em)
		#diagram(spacing:(0.5em, 1.5em),
			node((1, 0), [$f(a b+a c)$]), edge($a$, "->"), edge((2,1), $a$, "->"),
			node((0, 1), [$g(b)$]), edge("-/->"),
			node((0, 2)),
			node((2, 1), [$g(c)$]), edge($b$, "->"),
			node((2, 2), [$0$])
		)
]
---
#example(title:"With more than one premise per variable")[
	#set align(center)
	#grid(columns: 5,
		$... +$,
		h(2em),
		onerule(
			name:$forall a$,
			$f'(x) ->^a g'(y)$,
			$x ->^a y$
		),
		h(3em),
		onerule(
			$g'(x) ->^a x'+x''$,
			$x ->^b x'$,
			$x ->^c x''$
		)
	)
	#pause	
		#diagram(spacing:(0.5em,1.5em),
			node((1, 0), [$f'(a(b+c))$]), edge($a$, "->"),
			node((1, 1), [$g'(b+c)$]), edge($a$, "->"), 
			node((1, 2), $0+0$)
		) #h(3em)
		#diagram(spacing:(0.5em, 1.5em),
			node((1, 0), [$f'(a b+a c)$]), edge($a$, "->"), edge((2,1), $a$, "->"),
			node((0, 1), [$g'(b)$]), edge("-/->"),
			node((0, 2)),
			node((2, 1), [$g'(c)$]), edge("-/->"),
			node((2, 2))
		)
]

== Abstract Trace Semantics

- abstract? #pause

#remark(title:[B. Klin, 2005 and 2009])[
  test suites and logical distributive laws
] #pause

- recall behaviour $k : X -> H X = cal(P)(X)^L pause ≅ (cal(P)_"ne" (X)+1)^L = B T X$
	- $T = cal(P)_"ne"$: *effectful/branching* behaviour (non-determinism)
	- $B = (-+1)^L$: *pure* behaviour (labels and termination) #pause

- $ν B = frak(T)$ set of (partial finite) traces: final $B$-coalgebra #pause

- categories of algebras (Eilenberg-Moore) $Set^T = CSLat$ category of unbounded complete semi-lattices #pause

- $B$ lifts (with $δ^B : T B → B T$) and $nu overline(B) = nu B$

---

- abstract GSOS theory in $CSLat$:
$ overline(ρ) : overline(Σ)(X × overline(B) X) → overline(B)(overline(Σ)^star X) $ #pause

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

- $"tr" : μ Σ →^ξ μ overline(Σ) →^τ ν B$ #pause

- left square $⇒$ $"tr"$ is a congruence #emoji.face #pause

- how to get $overline(ρ)$ natural transformation in $CSLat$?

== Trace-GSOS

- rule format 
	#grid(columns: (1fr, 2fr), 
[
- for each $x_i$ and for each $a$, either $x_i ->^(a) y$ or $x_i ↛^a$
],
[	#set align(center)
	#onerule(
      $sigma(x_1 ... x_n) ->^c u$,
      $x_1 ->^(a_1) y_1$,
	  $...$,
	  $x_1 ->^(a_k) y_k$,
	  $x_1 ↛^(b_1)$,
	  $...$,
	  $quad$,
	  $x_2  ...$,
	  $quad$,
	  $...$
  )
  ])
  #pause 

#remark[Only *pure* premises: observe each variable at each label *once and only once* ]
#pause

- natural transformation
#only("1-3")[$ ρ : Σ(X × H X) → H Σ^star X $]
#only("4")[$ ρ : Σ(X × B T X) → B T Σ^star X $]
#only("5-")[$ ρ : Σ(X × B X) → B T Σ^star X $]

#pause #pause #pause
- De Simone rules $→$ Trace-GSOS rules:
$ cal(S)(r) = { r' "Trace-GSOS rule" | "each premise of" r "is a premise of" r' } $ 

---

- characterize "good" Trace-GSOS specifications: smooth and minimally linear#pause

#theorem[
	"good" Trace-GSOS specifications $⟺$ De Simone specifications
]
#pause
#theorem[
	"good" Trace-GSOS specifications $⟹$ $ρ$ yields a *natural* transformation $overline(ρ)$ in $CSLat$
	$ overline(ρ) : Σ(X × B X) ->^(ρ) B T Σ^⋆ X -->^(B T ξ_X) B T overline(Σ)^⋆ X -->^(B σ_X) B overline(Σ)^⋆ X $
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