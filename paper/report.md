# Sharp Volume Contraction of a Centrally Cut John Ellipsoid

*Explicit certificates, equality, and quantitative stability*

Zhou Longfei · Research report · 9 November 2026

### Abstract

For a convex body $K\subset\mathbb R^n$, let $w(K)$ be the volume of its maximum-volume inscribed ellipsoid. We determine the sharp ratio $w(K\cap H)/w(K)$ for a halfspace cut through that ellipsoid's center: it is $\frac12(n/(n-1))^{(n-1)/2}$ for $n\ge2$, and $1/2$ for $n=1$. We also establish an exact volume-deficit identity that yields the full equality classification, including nonsimplex extremizers, and dimension-independent stability of the new ellipsoid and its weighted contact geometry. The result refines the optimal dimension-independent bound established in the author's earlier joint work on Khachiyan's ellipsoid conjecture and clarifies the geometric progress of the method of inscribed ellipsoids. The sharp contraction theorem, equality classification, stability estimates, and supporting results have been formally verified in Lean 4 using mathlib.

The proof starts from John's finite contact characterization and reduces the extremal problem to contact polytopes without changing its sharp constant. An explicit transformation of the contact directions, followed by a common polar rotation, constructs a feasible positive-definite certificate. A quantitative determinant estimate links this certificate to a nonnegative contact defect. The logarithmic volume deficit then separates into geometric loss, cone complementarity, and matrix divergence. The supporting estimates use moment identities, Gram matrices, weighted Cauchy–Schwarz, and scalar interpolation with exact rational bounds.

**Keywords:** maximum-volume inscribed ellipsoid; central cut; John decomposition; conic certificate; determinant inequality; equality; stability.

## 1. Introduction

### 1.1. Central cuts, ellipsoid computation, and rounding

A convex body is a compact convex subset of $\mathbb R^n$ with nonempty interior. Let $J(K)$ be its unique maximum-volume inscribed ellipsoid, let $c(K)$ be its center, and set

```math
w(K)=\operatorname{vol}J(K)
=\max\{\operatorname{vol}E:E\subseteq K,\ E\text{ is an ellipsoid}\},
\tag{1.1}
```

where $\operatorname{vol}$ denotes Lebesgue volume. Existence, uniqueness, and the contact characterization are classical [John1948; GG2007]. We study the change in $w$ under a halfspace cut whose boundary contains $c(K)$.

Such cuts arise in localization methods for convex optimization. An oracle supplies a halfspace containing the target set, and the current region is replaced by its intersection with that halfspace. The choice of center controls the geometric progress. In the centroid method, Grünbaum's theorem bounds the surviving ordinary-volume fraction by $1-(n/(n+1))^n<1-e^{-1}$ [Grunbaum1960], but computing the centroid is expensive. The classical enclosing-ellipsoid method admits an $O(n^2)$ arithmetic update, with a dimension-dependent contraction factor [GLS1988; Todd2023]. Analytic and volumetric centers offer other computational tradeoffs [BV2004; AV1995; Vaidya1996; Anstreicher1997].

The method of inscribed ellipsoids instead uses $c(K)$ and the potential $w(K)$ [TKE1988]. It also provides a geometric normalization. If $J(K)=c+AB_2^n$, John's rounding theorem gives

```math
c+AB_2^n\subseteq K\subseteq c+nAB_2^n,
\qquad
B_2^n\subseteq A^{-1}(K-c)\subseteq nB_2^n.
\tag{1.2}
```

For a centrally symmetric body, the factor $n$ improves to $\sqrt n$. This rounding is useful in geometric preconditioning, volume approximation, and fixed-dimensional integer programming [GG2007; KT1993].

For a polytope with $N$ inequalities, computing $J(K)$ is a finite convex optimization problem; Section 2 gives its formulation and dual certificates. Interior-point methods exploit its structure [NN1994; KT1993; ZG2003]. One established bound computes an ellipsoid of volume at least $e^{-\delta}w(K)$, $0<\delta<1$, under a known normalization $B_2^n\subseteq K\subseteq\Lambda B_2^n$, within $O(N^{7/2}\log(N\Lambda/\delta))$ arithmetic operations [Anstreicher2002]. This is a bound for approximate ellipsoid computation. The contraction theorem below concerns the exact John center; relating a computed center to an admissible cut requires the corresponding approximation analysis. Section 7 distinguishes this computational cost from the number of exact central cuts.

Khachiyan asked for the optimal dimension-independent contraction factor [Khachiyan1990]. Zhou, Zou, and Liu proved the value $\sqrt e/2$ and its uniform optimality [Zhou2026]. The present report determines the exact value in each dimension and describes the geometry of equality and near equality.

### 1.2. Contributions

The results follow two connected threads.

1. **Sharp central-cut contraction.** Let $C_n$ be the supremum of $w(K\cap H)/w(K)$ over convex bodies and halfspaces through their John centers. We prove

   ```math
   C_n=R_n,\qquad R_1=\frac12,\qquad
   R_n=\frac12\left(\frac n{n-1}\right)^{(n-1)/2}\quad(n\ge2),
   \tag{1.3}
   ```

   with attainment in every dimension. The same sharp constant is obtained by restricting the supremum to finite John contact polytopes: the reduction in Section 2.4 preserves the original ellipsoid volume while enlarging the cut region. The proof constructs an explicit conic certificate from the resulting finite data and bounds its determinant. A simple extremal configuration determines the candidate ellipsoid and the certificate parameters.

2. **Equality and stability from an exact deficit.** The logarithmic shortfall from $R_n$ is the sum of a geometric determinant deficit, a cone-complementarity term, and a positive-definite matrix divergence. Their zero sets give all equality cases, including nonsimplex extremizers. Their quantitative control yields dimension-independent bounds for the new ellipsoid's shape and center and for the weighted contact geometry.

John's theorem and the finite convex optimization model are background. The problem-specific contribution is the quantitative certificate estimate and the geometric structure that it reveals.

### 1.3. Proof organization

Section 2 develops the optimization framework, proves exactness of the
certificate, and reduces the geometry to finite John contact data. Section 3
proves the sharp contraction using the frame estimate. Sections 4–6 derive
the exact deficit, equality, and stability; Section 7 gives iteration and
computational consequences. Section 8 proves the determinant estimate,
with higher dimensions before the low-dimensional block analysis, and
Section 9 supplies the stability estimates. Section 10 discusses extensions
and further matrix properties. Section 11 concludes.

## 2. Ellipsoid optimization and upper-bound certificates

The same optimization problem appears twice: first when choosing a center, and again when recomputing the largest inscribed ellipsoid after a cut. We begin with its variables and constraints, then derive the short inequality used throughout the report.

### 2.1. From containment to a convex problem

Throughout, the dimension is a positive integer. Let $B_2^n=\{z:\|z\|_2\le1\}$ be the closed Euclidean unit ball. Write

```math
\mathcal E(c,A)=c+AB_2^n,\qquad A\in\mathbb S_{++}^n,
\qquad \operatorname{vol}\mathcal E(c,A)=\kappa_n\det A,
\quad \kappa_n=\operatorname{vol}(B_2^n).
\tag{2.1}
```

The matrix $A$ is the linear map applied to the ball. Its eigenvalues are the semiaxis lengths. For a single inequality $g^Tx\le\beta$, containment is equivalent to

```math
\max_{\|z\|\le1}g^T(c+Az)=g^Tc+\|Ag\|\le\beta.
\tag{2.2}
```

Thus, for a bounded full-dimensional polytope
$\mathcal P=\{x:g_r^Tx\le\beta_r,\ r=1,\ldots,N\}$, the ellipsoid problem is

```math
\begin{aligned}
\text{maximize}_{c,\ A\succ0}\quad&\log\det A\\
\text{subject to}\quad&g_r^Tc+\|Ag_r\|\le\beta_r,
\qquad r=1,\ldots,N.
\end{aligned}
\tag{2.3}
```

The objective is concave and the constraints are convex [BV2004, Section 8.4.2]. Each support constraint is also a second-order-cone constraint:
$(\beta_r-g_r^Tc,Ag_r)\in\mathcal L_{n+1}$, where
$\mathcal L_{n+1}=\{(\tau,z):\tau\ge\|z\|\}$.
We remove redundant inequalities with $g_r=0$.

### 2.2. A certificate cancels the unknown center

To bound the volume of every feasible ellipsoid, assign a scalar $\alpha_r$ and
a vector $q_r$ to each supporting inequality. With
$\operatorname{sym}X=(X+X^T)/2$, the complete certificate conditions are

```math
\begin{gathered}
\sum_r\alpha_rg_r=0,\qquad \sum_r\alpha_r\beta_r=n,\\
\|q_r\|\le\alpha_r\quad\text{for every }r,\\
M=\sum_r\operatorname{sym}(q_rg_r^T)\succ0.
\end{gathered}
\tag{2.4}
```

Balance cancels the unknown center, and the second equality fixes the scale.
The norm inequality is the second-order-cone constraint
$(\alpha_r,q_r)\in\mathcal L_{n+1}$; it also implies $\alpha_r\ge0$.
The final condition collects the directional information into a positive-definite
matrix. Thus (2.4) includes every constraint used by the dual problem below.

<a id="lem-certificate"></a>
**Lemma 2.1 (volume certificate).** If (2.4) holds, every feasible ellipsoid in (2.3) satisfies

```math
\operatorname{tr}(AM)\le n,\qquad
\det A\le\frac1{\det M}.
\tag{2.5}
```

**Proof.** The two conclusions require two steps: first turn the support
constraints into a trace bound, then apply scalar AM–GM to obtain a determinant
bound. Aggregate the support inequalities; balance cancels the center:

```math
\begin{aligned}
\operatorname{tr}(AM)
&=\sum_r q_r^TAg_r
\le\sum_r\alpha_r\|Ag_r\|\\
&\le\sum_r\alpha_r(\beta_r-g_r^Tc)
=n-c^T\sum_r\alpha_rg_r=n.
\end{aligned}
\tag{2.6}
```

To pass from trace to determinant, use the symmetric positive-definite matrix
$Y=M^{1/2}AM^{1/2}$. Its trace and determinant are the quantities we need.
For its eigenvalues $\rho_1,\ldots,\rho_n>0$, scalar AM–GM gives

```math
\det A\det M=\det Y=\prod_{j=1}^n\rho_j
\le\left(\frac1n\sum_{j=1}^n\rho_j\right)^n
=\left(\frac{\operatorname{tr}(AM)}n\right)^n\le1.
\tag{2.7}
```

Dividing by $\det M>0$ proves (2.5). ∎

The matrix $M$ is a certificate: checking its finite constraints is enough to bound the optimum. A larger determinant gives a stronger bound. Optimizing the certificate leads to the normalized dual problem

```math
\text{maximize }\log\det M
\quad\text{over }(\alpha_r,q_r)\text{ satisfying (2.4)}.
\tag{2.8}
```

### 2.3. Exact certificates and optimal contacts

Optimizing the certificate recovers the ellipsoid optimum exactly. We prove
this by constructing multipliers from the contacts of the optimal ellipsoid.
The only geometric ingredient is the following classical characterization.

<a id="lem-john"></a>
**Lemma 2.2 (John's contact characterization [John1948; GG2007, Theorems 3.1 and 3.3]).**
Let $K\subset\mathbb R^n$ be a convex body containing $B_2^n$.
Then $J(K)=B_2^n$ if and only if there are finitely many unit vectors
$u_i\in\partial K\cap S^{n-1}$ and positive weights $\lambda_i$ such that

```math
u_i^Tx\le1\ (x\in K),\qquad
\sum_i\lambda_i u_i=0,\qquad
\sum_i\lambda_i u_i u_i^T=I,
\qquad \sum_i\lambda_i=n.
\tag{2.9}
```

We use this standard result without proof. The last identity follows by taking
traces in the second-moment identity. We call finite unit vectors and positive
weights with the two moment identities a *John frame*; the inequalities in
(2.9) say that the frame supports $K$. The same vector $u_i$ specifies both
the point of tangency with the unit ball and the outward normal of its
supporting plane.

**Construct an optimal certificate.** Return to the bounded full-dimensional
polytope $\mathcal P$ of (2.3). The next proposition proves attainment and
equality of the primal and normalized dual values.

<a id="prop-exact-duality"></a>
**Proposition 2.3 (optimal multipliers from John contacts).** Problems (2.3) and (2.8) attain their optima. If $\mathcal E(c,A)=J(\mathcal P)$, there are normalized dual multipliers with aggregate $M=A^{-1}$ and zero cone pairings. Hence the optimal values of (2.3) and (2.8) sum to zero.

**Proof.** Construct the dual variables from the contacts of the actual
optimal ellipsoid. We first identify the active facet normal for each contact,
then rescale the John weights so that their moments become the dual constraints.

**Identify the active facets.** Let $\mathcal E(c,A)=J(\mathcal P)$,
whose existence is classical, and apply John's characterization to
$A^{-1}(\mathcal P-c)$. A unit contact $p$ lies on some defining plane.
For its index $r$,

```math
\|Ag_r\|\le\beta_r-g_r^Tc=(Ag_r)^Tp
\le\|Ag_r\|\|p\|=\|Ag_r\|.
\tag{2.10}
```

Hence $p=Ag_r/\|Ag_r\|$ and the plane is active. Assign contacts to such indices and combine their weights. Writing $\ell_r=\|Ag_r\|>0$, this gives

```math
p_r=\frac{Ag_r}{\ell_r},\qquad
\sum_r\mu_rp_r=0,\qquad
\sum_r\mu_rp_rp_r^T=I,\qquad \sum_r\mu_r=n.
\tag{2.11}
```

**Turn contact weights into multipliers.** The weights satisfy $\mu_r\ge0$ and
$\mu_r(\beta_r-g_r^Tc-\ell_r)=0$. Dividing by the active support length
$\ell_r$ makes the zero first moment become dual balance.
Define $\alpha_r=\mu_r/\ell_r$ and $q_r=\alpha_rp_r$. Then

```math
\begin{aligned}
\sum_r\alpha_rg_r&=A^{-1}\sum_r\mu_rp_r=0,\\
\sum_r\alpha_r\beta_r
&=c^T\sum_r\alpha_rg_r+\sum_r\mu_r=n,\\
\|q_r\|&=\alpha_r,\\
\alpha_r(\beta_r-g_r^Tc)-q_r^TAg_r
&=\alpha_r(\beta_r-g_r^Tc-\ell_r)=0.
\end{aligned}
\tag{2.12}
```

**Use isotropy to match the inverse shape.** The second moment supplies the
remaining dual matrix equation. Since $g_r=\ell_rA^{-1}p_r$, the aggregate is

```math
\sum_rq_rg_r^T=\sum_r\mu_rp_rp_r^TA^{-1}=A^{-1}.
\tag{2.13}
```

The cone constraints and zero pairings follow immediately. Lemma 2.1 now proves that this normalized certificate is dual optimal and that the gap is zero. ∎

**Recover contacts from an optimal pair.** The converse identifies the active
supports and shows that the normalized directions recover a John frame.

<a id="prop-kkt"></a>
**Proposition 2.4 (optimality and contact recovery).** A feasible pair for (2.3) and (2.8) is optimal if and only if

```math
M=A^{-1},\qquad
\alpha_r(\beta_r-g_r^Tc)-q_r^TAg_r=0\quad\text{for every }r.
\tag{2.14}
```

For each $\alpha_r>0$,

```math
\beta_r-g_r^Tc=\|Ag_r\|,\qquad
q_r=\alpha_r\frac{Ag_r}{\|Ag_r\|}.
\tag{2.15}
```

With $p_r=Ag_r/\|Ag_r\|$ and $\mu_r=\alpha_r\|Ag_r\|$, the vectors and weights satisfy (2.11).

**Proof.** At a primal–dual optimum, Proposition 2.3 gives
$\det A\det M=1$. Equality throughout the trace–AM–GM chain (2.7) then forces
$Y=M^{1/2}AM^{1/2}=I$ and $\operatorname{tr}(AM)=n$.
The cone pairings are nonnegative and, by balance and normalization, their
sum is $n-\operatorname{tr}(AM)=0$. Thus every pairing vanishes.
Conversely, $M=A^{-1}$ gives equality in the certificate bound, proving
optimality of the feasible pair. For $\alpha_r>0$, equality in the support
and Cauchy–Schwarz inequalities gives (2.15).

The remaining point is to recover the full second moment from the symmetrized
aggregate. To recover isotropy, set $T=\sum_r\alpha_rg_rg_r^T/\|Ag_r\|$.
The aggregate equation is a Sylvester equation for $T$:
$AT+TA=2A^{-1}$. For $H=T-A^{-2}$, therefore,

```math
AH+HA=0,
\qquad
0=\operatorname{tr}\bigl(H(AH+HA)\bigr)
=2\operatorname{tr}(AH^2)
\ge2\lambda_{\min}(A)\|H\|_F^2.
\tag{2.16}
```

Thus $H=0$ and $T=A^{-2}$. Positive definiteness has determined the
unsymmetrized moment matrix without a commutativity assumption.
The contact moments follow:

```math
\sum_r\mu_rp_r=A\sum_r\alpha_rg_r=0,
\qquad
\sum_r\mu_rp_rp_r^T=ATA=I,
\qquad
\sum_r\mu_r=\operatorname{tr}I=n.
\tag{2.17}
```

This proves (2.11). ∎

These results explain the exact optimization meaning of the certificate.
The universal contraction proof in Section 3 uses Lemma 2.1 and one explicit
feasible certificate; it does not require solving the normalized dual.
Section 10.1 gives the usual unnormalized dual and its scale reduction.

### 2.4. Finite contact reduction

An invertible affine change of coordinates preserves ratios of ellipsoid
volumes. Send $J(K)$ to the unit ball and apply Lemma 2.2.
The resulting supporting frame converts the geometric problem into a finite
polytope problem while preserving the sharp supremum.

The frame does not need to describe the whole boundary of $K$. Retaining only
these supporting planes produces a polytope containing $K$, while John's
characterization certifies that its original maximal ellipsoid is unchanged.

<a id="lem-reduction"></a>
**Lemma 2.5 (finite contact reduction).** Let $K$ be a convex body with
$J(K)=B_2^n$, and let $\mathcal U$ be a supporting John frame from Lemma 2.2.
Then the contact polytope defined below is a convex body satisfying

```math
P_{\mathcal U}=\{x:u_i^Tx\le1\text{ for all }i\},\qquad
K\subseteq P_{\mathcal U},\qquad J(P_{\mathcal U})=B_2^n.
\tag{2.18}
```

In particular, $w(P_{\mathcal U})=w(K)=\kappa_n$. For every central halfspace
$H_v=\{x:v^Tx\le0\}$ with $\|v\|=1$, each ellipsoid in $K\cap H_v$ is also
feasible in $P_{\mathcal U}\cap H_v$, so
$w(K\cap H_v)\le w(P_{\mathcal U}\cap H_v)$.
Both cut sets have nonempty interior because they contain the corresponding
half of the unit ball.

**Proof.** The main point is boundedness: the supporting halfspaces could
otherwise define an unbounded set. We obtain a radius bound directly from
the two John moments. Since $\|u_i\|=1$, the polyhedron contains $B_2^n$.
For $x\in P_{\mathcal U}$, put $r=\|x\|$ and $s_i=u_i^Tx$. Then
$-r\le s_i\le1$, $\sum_i\lambda_i s_i=0$, and $\sum_i\lambda_i s_i^2=r^2$.
The product $(1-s_i)(r+s_i)$ is nonnegative and quadratic in $s_i$, so its
weighted sum can be evaluated using exactly these moments:

```math
\begin{aligned}
0\le\sum_i\lambda_i(1-s_i)(r+s_i)
&=r\sum_i\lambda_i+(1-r)\sum_i\lambda_i s_i-\sum_i\lambda_i s_i^2\\
&=nr-r^2.
\end{aligned}
\tag{2.19}
```

Thus $r(r-n)\le0$ and $r\ge0$ imply $r\le n$. The finite intersection is closed and convex, so $B_2^n\subseteq P_{\mathcal U}\subseteq nB_2^n$ makes it a convex body. John's characterization gives $J(P_{\mathcal U})=B_2^n$, and the supporting inequalities give $K\subseteq P_{\mathcal U}$. ∎

**Why the reduction preserves the sharp constant.** The enlargement can increase
the post-cut ellipsoid volume, but it leaves the pre-cut volume unchanged.
Consequently,

```math
\frac{w(K\cap H_v)}{w(K)}
\le\frac{w(P_{\mathcal U}\cap H_v)}{w(K)}
=\frac{w(P_{\mathcal U}\cap H_v)}{w(P_{\mathcal U})}.
\tag{2.20}
```

For a particular $K$ the inequality can be strict. For the extremal problem,
however, the two classes have the same supremum. Every normalized convex body
admits such an enlargement. Conversely, any John frame defines a convex body
$P_{\mathcal U}$ with John ellipsoid $B_2^n$: the boundedness argument above
uses only the frame identities, and Lemma 2.2 identifies its ellipsoid.
Thus contact polytopes themselves belong to the original class, and

```math
C_n
=\sup_{\substack{\mathcal U\ \text{a John frame}\\\|v\|=1}}
\frac{w(P_{\mathcal U}\cap H_v)}{w(P_{\mathcal U})}
=\sup_{\substack{\mathcal U\ \text{a John frame}\\\|v\|=1}}
\frac{w(P_{\mathcal U}\cap H_v)}{\kappa_n}.
\tag{2.21}
```

The first direction gives an upper bound for every convex body; the converse
shows that no sharpness is lost. For each fixed frame and cut,
$w(P_{\mathcal U}\cap H_v)/\kappa_n$ is the maximum feasible determinant
in the finite ellipsoid problem (2.3), with supporting
inequalities $(g_i,\beta_i)=(u_i,1)$ and the one added cut $(g_0,\beta_0)=(v,0)$.
The geometric problem has therefore become a universal inequality for finite
contact data. It is this finite problem that the next section certifies.

## 3. The sharp central-cut bound

We now apply the certificate framework to a cut through the John center. The proof has a simple overall structure: normalize the old ellipsoid, construct a certificate from its contacts, and bound the determinant of that certificate. A model example will first show where the sharp constant comes from.

### 3.1. Statement and normalization

<a id="thm-sharp"></a>
**Theorem 3.1 (sharp central-cut contraction).** Let $K\subset\mathbb R^n$, $n\ge1$, be a convex body, and let $H$ be a closed halfspace whose boundary passes through $c(K)$. Then

```math
w(K\cap H)\le R_nw(K),
\tag{3.1}
```

where $R_n$ is given by (1.3). For every fixed dimension, there are bodies and central cuts attaining equality.

**Proof arrangement.** The proof is developed in Sections 3.1–3.4 and
completed in Section 3.4. It uses Theorem 3.2, whose proof is deferred to
Section 8.

For $n\ge2$, take John coordinates so that $J(K)=B_2^n$, and write
$H=H_v=\{x:v^Tx\le0\}$ with $\|v\|=1$. A candidate $\mathcal E(c,A)$ then has relative volume $\det A$. It is enough to prove $\det A\le R_n$ for every candidate in $K\cap H_v$. The cut body has nonempty interior: it contains, for example, the ball with center $-v/4$ and radius $1/8$.

### 3.2. A model that explains the constant

We assume $n\ge2$ in the certificate, equality, and stability arguments of Sections 3.2–6.

Put $b=1/n$ and let $P=I-vv^T$ be the orthogonal projection onto $v^\perp$. Consider the candidate

```math
c_*=-\frac12v,\qquad
A_*=\frac12vv^T+\frac1{\sqrt{1-b}}P,
\qquad \det A_*=R_n.
\tag{3.2}
```

Its center moves away from the cutting plane by $1/2$. Its axial semiaxis is $1/2$, so it touches the cut; its transverse semiaxes expand to $(1-b)^{-1/2}$. The product of these lengths is the proposed sharp factor.

Take a regular simplex circumscribed about the unit ball, with unit facet normals $u_1,\ldots,u_{n+1}$. Its standard contact identities are

```math
u_i^Tu_j=-\frac1n\ (i\ne j),\qquad
\sum_i u_i=0,\qquad
\sum_i u_i u_i^T=\frac{n+1}{n}I.
\tag{3.3}
```

Thus $\lambda_i=n/(n+1)$ are John weights. Choose $v=-u_1$, so the contact heights are $-1$ and $b$. The three required support values are

```math
\begin{aligned}
(-v)^Tc_*+\|A_*(-v)\|&=\frac12+\frac12=1,\\
u_i^Tc_*+\|A_*u_i\|
&=-\frac b2+\sqrt{\frac{b^2}{4}+\frac{1-b^2}{1-b}}=1
&& (u_i^Tv=b),\\
v^Tc_*+\|A_*v\|&=-\frac12+\frac12=0.
\end{aligned}
\tag{3.4}
```

Hence $\mathcal E(c_*,A_*)\subseteq\Delta\cap H_v$ and
$w(\Delta\cap H_v)/w(\Delta)\ge\det A_*=R_n$.

![A normalized triangle and the translated, wider ellipse retained after its central cut.](figures/central_cut.png)

*Figure 1. The model in dimension two. The original inball has radius one. The new candidate has semiaxes $1/2$ and $\sqrt2$, so its area ratio is $1/\sqrt2$. The cut bisects the old ellipsoid, but the new ellipsoid can use space in the surrounding body.*

The same support calculation applies to any John frame whose contacts have heights $-1$ and $b$. Section 5 will describe all such equality configurations. For later use, write the inverse model shape as
$M_0=A_*^{-1}=2vv^T+\sqrt{1-b}\,P$.

### 3.3. Constructing a certificate for an arbitrary frame

Let $(u_i,\lambda_i)$ be any supporting John frame. Define its axial and transverse components by $s_i=u_i^Tv$ and $y_i=Pu_i$. Old supporting planes carry the index $i$; the added cut has the separate label $0$.

The equality model tells us what the certificate should become:
$M_0=A_*^{-1}$. We seek formulas depending only on the original frame and the
cut, valid for every frame and matching that inverse shape at the model.
The scalar weights enforce balance; the vector directions enforce cone
feasibility and the model support relations.

**Balance the scalar weights.** Tilting the old weights linearly with the
contact height shifts their weighted normal sum in the direction $-v$.
The new cut, whose normal is $v$, can then restore balance. The John moments
evaluate both sums exactly. Choose

```math
t=\frac{1+b}{2},\qquad
\alpha_i=\lambda_i(1-ts_i)\ge\lambda_i(1-t)\ge\frac{\lambda_i}{4},
\qquad \alpha_0=t.
\tag{3.5}
```

The John moments give normalization and balance directly:

```math
\begin{aligned}
\sum_i\alpha_i
&=\sum_i\lambda_i-t\sum_i\lambda_i s_i=n,\\
\sum_i\alpha_i u_i+tv
&=\sum_i\lambda_i u_i-t\left(\sum_i\lambda_i u_iu_i^T\right)v+tv=0.
\end{aligned}
\tag{3.6}
```

The cut has right-hand side zero, so its weight does not enter the first sum.
The two identities are exactly the normalization and balance conditions in
(2.4). The bound $\alpha_i\ge\lambda_i/4$ keeps every original contact present
and will later control support slacks in the stability argument.
Balance alone allows other values of $t$; matching the equality model fixes
the value in (3.5), as explained below.

**Choose admissible vector directions.** We need unit directions for cone
feasibility: then the provisional choice $q_i=\alpha_i p_i$ lies on the
boundary of the cone. At equality these directions must also be
$A_*u_i/\|A_*u_i\|$, so that the support Cauchy–Schwarz inequality is exact.
The following transformation changes the axial coordinate while preserving
the unit sphere:

```math
a=\frac b{2-b},\qquad k=\sqrt{1-a^2},\qquad
p_i=\frac{(s_i-a)v+ky_i}{1-as_i}.
\tag{3.7}
```

Since $\|y_i\|^2=1-s_i^2$ and $1-as_i\ge1-a\ge2/3$, the directions are well defined and

```math
\|p_i\|^2
=\frac{(s_i-a)^2+(1-a^2)(1-s_i^2)}{(1-as_i)^2}=1.
\tag{3.8}
```

This is the unit-direction form of a Lorentz transformation. It fixes the
pole $-v$. At the model latitude, the required axial coordinate is
$b/(2+b)$, since $\|A_*u_i\|=1+b/2$ there. Matching
$(b-a)/(1-ab)=b/(2+b)$ gives the chosen $a=b/(2-b)$ and ensures

```math
s_i\in\{-1,b\}\quad\Longrightarrow\quad
p_i=\frac{A_*u_i}{\|A_*u_i\|},
\tag{3.9}
```

the contact direction required at the model optimum. The transverse John
moment then shows that matching the transverse part of $M_0$ requires
$1-tb=(1-b)(1+b/2)$, which gives $t=(1+b)/2$.
Thus the parameters in (3.5) and (3.7) are fixed by exact model matching,
while the balance and unit-norm identities remain valid for arbitrary frames.

**The contact defect $\chi$.** To extend model matching to a quantitative
statement for arbitrary contacts, introduce

```math
\chi=\sum_i\lambda_i\frac{(1+s_i)(s_i-b)^2}{1-as_i}.
\tag{3.10}
```

The factors $1+s_i$ and $(s_i-b)^2$ make each contribution vanish at the
model pole and latitude. The positive denominator is the same one appearing
in the transformed directions. This choice makes $\chi$ compatible with
the moment calculations of Section 8, while preserving
$\chi=0\iff s_i\in\{-1,b\}$ for every contact.

The defect depends only on the original weighted contact geometry and the
cut direction. It will control the determinant excess, identify all equality
frames, and bound weighted distances from those frames. It is therefore the
common geometric quantity behind the sharp bound, equality, and stability.

**The aggregate matrix $Q$.** Collect the original normals and their
transformed directions into one matrix:

```math
Q=\sum_i\alpha_i u_ip_i^T+t\,vv^T.
\tag{3.11}
```

Each term $\alpha_i u_ip_i^T$ records one original constraint and its proposed
dual direction; the term $tvv^T$ represents the new cut.
Thus $Q^T$ is the aggregate of the unrotated vector multipliers.
Like $\chi$, it contains no unknown center or shape of the recomputed ellipsoid.

The following theorem supplies invertibility and a determinant lower bound.
Section 3.4 will then use one common rotation to turn $Q^T$ into a
positive-definite certificate with the same determinant. This is how the finite
contact construction bounds every feasible cut ellipsoid without solving the
new optimization problem. The central estimate links its volume certificate,
$\log(R_n\det Q)$, to the contact defect $\chi$.

<a id="thm-frame-bound"></a>
**Theorem 3.2 (John-frame certificate bound).** The matrix $Q$ is invertible with positive determinant. For $d=2-b$,

```math
\frac{\chi}{1500}\le\log(R_n\det Q)\le\frac{\chi}{2d}.
\tag{3.12}
```

In particular, $\det Q\ge R_n^{-1}$. Equality in this determinant bound holds if and only if every contact has height $-1$ or $b$; then $Q=M_0$.

**Proof deferred to Section 8.** Theorem 8.1 there is the normalized version
of this estimate. Section 8.6 proves its equivalence to (3.12) and completes
Theorem 3.2, including the equality statement. We first use the result to
finish the geometric proof of Theorem 3.1.

### 3.4. Completion of Theorem 3.1: a common rotation

The matrix $Q^T$ need not be symmetric. A single rotation of all the directions produces the positive-definite aggregate required by Lemma 2.1. By Theorem 3.2, the left polar decomposition is well defined:

```math
M=(QQ^T)^{1/2},\qquad U=M^{-1}Q,
\qquad q_i=\alpha_iUp_i,\qquad q_0=tUv.
\tag{3.13}
```

Orthogonality follows from

```math
UU^T=M^{-1}QQ^TM^{-1}=I,
\tag{3.14}
```

and hence $\|q_i\|=\alpha_i$, $\|q_0\|=t$. The aggregate is

```math
\sum_iq_iu_i^T+q_0v^T=UQ^T=M^{-1}QQ^T=M.
\tag{3.15}
```

The scalar weights remain balanced, and

```math
\det M=\sqrt{\det(QQ^T)}=|\det Q|=\det Q\ge R_n^{-1}.
\tag{3.16}
```

We now have every part of the certificate: normalization, balance, cone feasibility, positive definiteness, and a lower bound on its determinant.

**Completion of Theorem 3.1.** Every ellipsoid in $K\cap H_v$ is feasible for the contact polytope and the cut. Lemma 2.1 gives

```math
\det A\le(\det M)^{-1}\le R_n.
\tag{3.17}
```

Since $w(K)=\kappa_n$ in John coordinates,

```math
\frac{w(K\cap H_v)}{w(K)}
=\max_{\mathcal E(c,A)\subseteq K\cap H_v}\det A\le R_n.
\tag{3.18}
```

The ratio is affine invariant, proving (3.1), and the simplex model attains it. For $n=1$, write $K=[\ell,r]$; then $J(K)=K$, $c(K)=(\ell+r)/2$, and $w(K\cap H)=(r-\ell)/2=w(K)/2$. ∎

The proof has also produced a quantitative object: the logarithmic determinant excess in (3.12). We next show that this excess is one part of an exact volume deficit. This is the starting point for equality and stability.

## 4. An exact deficit identity

The contraction theorem gives an upper bound. To understand equality and near equality, we need to identify where the proof can lose volume. The certificate separates these losses into three terms.

### 4.1. The two losses in the certificate inequality

For a feasible primal–dual pair in Section 2, let

```math
\tau_r=\beta_r-g_r^Tc,\qquad x_r=Ag_r,\qquad
\gamma_r=\alpha_r\tau_r-q_r^Tx_r\ge0,
\qquad Y=M^{1/2}AM^{1/2}.
\tag{4.1}
```

Each $\gamma_r$ is a cone pairing. The identities
$\operatorname{tr}Y=\operatorname{tr}(AM)$ and
$\det Y=\det A\det M$ give

```math
\begin{aligned}
\mathcal C&:=\sum_r\gamma_r
=\sum_r\alpha_r\beta_r-c^T\sum_r\alpha_rg_r-\operatorname{tr}(AM)\\
&=n-\operatorname{tr}(AM),\\
\mathcal D&:=\operatorname{tr}Y-n-\log\det Y\ge0,\\
G&:=-\log\det M-\log\det A=\mathcal C+\mathcal D.
\end{aligned}
\tag{4.2}
```

Here $\mathcal C$ records the slack in the aggregated support inequalities. The matrix divergence $\mathcal D$ records the slack in the spectral inequality $\log\det Y\le\operatorname{tr}Y-n$. Its nonnegativity follows from $r-1-\log r\ge0$ for each positive eigenvalue $r$. The gap $G$ is computable from a feasible ellipsoid and a feasible certificate.

### 4.2. Add the geometric loss

For the explicit certificate of Section 3, define
$\Delta_{\rm geom}=\log(R_n\det M)=\log(R_n\det Q)$. Theorem 3.2 proves that this term is nonnegative and controls $\chi$.

<a id="prop-gap"></a>
**Proposition 4.1 (exact volume deficit).** In John coordinates, every feasible cut ellipsoid satisfies

```math
\boxed{\epsilon:=\log\frac{R_n}{\det A}
=\Delta_{\rm geom}+\mathcal C+\mathcal D.}
\tag{4.3}
```

All three terms are nonnegative. For the actual new John ellipsoid, the same deficit is $\epsilon=\log(R_nw(K)/w(K\cap H))$ in the original coordinates.

**Proof.** Add the geometric loss to the primal–dual gap. The intermediate
certificate determinant cancels, leaving exactly the volume deficit:

```math
\begin{aligned}
\Delta_{\rm geom}+\mathcal C+\mathcal D
&=\log(R_n\det M)-\log\det M-\log\det A\\
&=\log\frac{R_n}{\det A}=\epsilon.
\end{aligned}
\tag{4.4}
```

At the new optimum, $\det A=w(K\cap H_v)/w(K)$. Affine invariance gives the stated interpretation. ∎

The three terms have distinct zero sets:

```math
\begin{aligned}
\Delta_{\rm geom}=0&\iff\chi=0\iff s_i\in\{-1,b\}\quad\forall i,\\
\mathcal C=0&\iff\gamma_r=0\quad\forall r,\\
\mathcal D=0&\iff Y=I\iff A=M^{-1}.
\end{aligned}
\tag{4.5}
```

Thus zero deficit imposes the model contact geometry, complementarity, and shape matching simultaneously. For small deficit, the same decomposition gives quantitative control; in particular, $\chi\le1500\Delta_{\rm geom}\le1500\epsilon$.

### 4.3. Small matrix divergence means close shape matching

We use $\|\cdot\|_F$ for the Frobenius matrix norm; vector norms are Euclidean.

<a id="lem-matching"></a>
**Lemma 4.2 (matrix matching).** For any normalized feasible pair, if $G\le1/4$, then

```math
\|M^{1/2}AM^{1/2}-I\|_F\le2\sqrt G.
\tag{4.6}
```

**Proof.** We first use the small divergence to bound each eigenvalue from
above. On that bounded range, the same scalar divergence controls squared
distance from $1$. Put $h(t)=t-1-\log t$.
Integrating $h'(t)=1-1/t$ on either side of $1$ gives

```math
h(t)\ge\frac{(t-1)^2}{2\max\{1,t\}}\quad(t>0),
\qquad h(2)=1-\log2>\frac14.
\tag{4.7}
```

For the eigenvalues $\rho_j>0$ of $Y$,
$\sum_jh(\rho_j)=\mathcal D\le G\le1/4$.
Since $h$ is increasing on $[1,\infty)$, each $\rho_j<2$. Hence

```math
\|Y-I\|_F^2=\sum_j(\rho_j-1)^2
\le4\sum_jh(\rho_j)=4\mathcal D\le4G.
\tag{4.8}
```

Taking square roots proves the claim. ∎

Section 9 also gives an exact sum-of-squares identity for each cone pairing and a corresponding weighted estimate for multiplier directions. For the geometric conclusions below, the essential point is already visible: a small gap enforces matrix matching, while the geometric part of the deficit controls how close $M$ is to the model certificate.

## 5. Equality and the family of extremizers

### 5.1. The complete equality condition

Continue in John coordinates and write

```math
\mathcal Z_b=\{-v\}\cup\{u\in S^{n-1}:u^Tv=b\}.
\tag{5.1}
```

This set consists of the pole opposite the cut direction and a latitude sphere. The extremal ellipsoid $\mathcal E(c_*,A_*)$ is the one defined in (3.2).

<a id="thm-equality"></a>
**Theorem 5.1 (equality classification).** A normalized body $K$ attains $w(K\cap H_v)=R_nw(K)$ if and only if it admits a John frame supported on $\mathcal Z_b$ such that

```math
\operatorname{conv}\bigl(B_2^n\cup\mathcal E(c_*,A_*)\bigr)
\subseteq K\subseteq P_{\mathcal U}.
\tag{5.2}
```

The new John ellipsoid is then exactly $\mathcal E(c_*,A_*)$. If equality holds, every positive-weight John frame supporting $K$ lies in $\mathcal Z_b$. For a contact polytope $P_{\mathcal U}$, equality is equivalent simply to its defining John frame being supported on $\mathcal Z_b$.

**Proof.** For necessity, zero deficit will first determine the contact heights
and ellipsoid shape, then the active supports will determine its center.
For sufficiency, the candidate ellipsoid in the sandwich already supplies the
required volume.

**Necessity: recover the shape and then the center.** Fix any supporting John
frame and suppose $\det A=R_n$. The deficit identity gives

```math
\begin{aligned}
\epsilon=0&\ \Longrightarrow\ \Delta_{\rm geom}=\mathcal C=\mathcal D=0\\
&\ \Longrightarrow\ \chi=0,\quad Q=M=M_0,\quad U=I,\quad A=A_*.
\end{aligned}
\tag{5.3}
```

The shape is now fixed. To recover the center, compare the active support
values with those of the model. Since $\alpha_i>0$ and
$p_i=A_*u_i/\|A_*u_i\|$, complementarity reduces to

```math
0=\gamma_i
=\alpha_i\bigl(1-u_i^Tc-\|A_*u_i\|\bigr),
\qquad
u_i^T(c-c_*)=0\quad\forall i.
\tag{5.4}
```

The second identity uses the model support equations. Isotropy now recovers the center:

```math
\|c-c_*\|^2
=\sum_i\lambda_i\bigl(u_i^T(c-c_*)\bigr)^2=0.
\tag{5.5}
```

Thus $\mathcal E(c_*,A_*)\subseteq K\cap H_v$, and convexity yields the left inclusion in (5.2). The right inclusion is (2.18). The frame was arbitrary, proving the asserted quantifier over every John frame.

**Sufficiency: use the included model ellipsoid.** Suppose (5.2) holds for a
John frame supported on $\mathcal Z_b$. John's characterization and the model
feasibility give

```math
w(K)=\kappa_n,\qquad
w(K\cap H_v)\ge\kappa_n\det A_*=R_n\kappa_n.
\tag{5.6}
```

Theorem 3.1 supplies the reverse inequality. For $K=P_{\mathcal U}$, model feasibility follows directly from the three support values in Section 3.2. ∎

The equality condition determines the new ellipsoid and the active contact geometry. It leaves freedom in the rest of the body, as the two inclusions in (5.2) show.

### 5.2. Extremizers beyond regular simplices

The latitude part of an equality frame can be built from any John frame in one lower dimension. This gives a concrete description of the freedom in Theorem 5.1.

<a id="prop-extremizers"></a>
**Proposition 5.2 (transverse construction).** Let unit vectors $w_i\in v^\perp$ and positive weights $\mu_i$ satisfy
$\sum_i\mu_iw_i=0$ and $\sum_i\mu_iw_iw_i^T=P$. Then the contacts

```math
u_i=bv+\sqrt{1-b^2}\,w_i,\qquad
\lambda_i=\frac{\mu_i}{1-b^2},\qquad
u_{\rm pole}=-v,\qquad \lambda_{\rm pole}=\frac1{1+b}
\tag{5.7}
```

form a John frame supported on $\mathcal Z_b$.

**Proof.** The weight rescaling compensates for the transverse length
$\sqrt{1-b^2}$, while the pole weight balances the axial first moment.
We check that the same choices also give the axial second moment.
The vectors have unit norm because $w_i\perp v$ and
$\|u_i\|^2=b^2+(1-b^2)\|w_i\|^2=1$. Taking traces in the transverse second moment gives

```math
\sum_i\mu_i=n-1=\frac{1-b}{b},\qquad
S:=\sum_i\lambda_i=\frac1{b(1+b)}.
\tag{5.8}
```

The pole and latitude contributions therefore satisfy

```math
\begin{aligned}
\lambda_{\rm pole}u_{\rm pole}+\sum_i\lambda_i u_i
&=\left(-\frac1{1+b}+bS\right)v
+\frac1{\sqrt{1-b^2}}\sum_i\mu_iw_i=0,\\
\lambda_{\rm pole}u_{\rm pole}u_{\rm pole}^T+\sum_i\lambda_i u_i u_i^T
&=\left(\frac1{1+b}+b^2S\right)vv^T+\sum_i\mu_iw_iw_i^T\\
&=vv^T+P=I.
\end{aligned}
\tag{5.9}
```

The mixed terms in the second line vanish by $\sum_i\mu_iw_i=0$. All weights are positive and all heights lie in $\{-1,b\}$. ∎

For example, take $w_i=\pm e_j$, $j=1,\ldots,n-1$, with $\mu_i=1/2$. In dimension three, set $v=e_3$. The four latitude contacts have John weight $9/16$ each, and the pole $-e_3$ has weight $3/4$. Their contact polytope is the square pyramid

```math
K=\{(x,y,z):z\ge-1,\quad
2\sqrt2|x|+z\le3,\quad 2\sqrt2|y|+z\le3\}.
\tag{5.10}
```

Its base vertices are $(\pm\sqrt2,\pm\sqrt2,-1)$ and its apex is $(0,0,3)$. Proposition 5.2 and Theorem 5.1 give $J(K)=B_2^3$ and

```math
\begin{gathered}
J(K\cap\{z\le0\})=c_*+A_*B_2^3,\qquad
c_*=-\frac12e_3,\\
A_*=\operatorname{diag}\!\left(\sqrt{\frac32},\sqrt{\frac32},\frac12\right),
\qquad \frac{w(K\cap\{z\le0\})}{w(K)}=\det A_*=\frac34=R_3.
\end{gathered}
\tag{5.11}
```

![A square pyramid with its unit John ball, and the retained square frustum with its translated, wider John ellipsoid after the cut z equals zero.](figures/square_pyramid.png)

*Figure 2. A square-pyramid extremizer in dimension three. (a) The unit ball touches four triangular side facets at height $z=1/3$ and the square base at $-e_3$. (b) The central cut leaves a square frustum. Its John ellipsoid touches the four sides, the base, and the cut; its semiaxes are $\sqrt{3/2},\sqrt{3/2},1/2$. Filled colored points mark contacts, and the open orange point marks the new center. Both panels use the same orthographic viewing direction, with an enlarged view in (b). This five-facet extremizer exhibits the freedom beyond the simplex model in Figure 1.*

The regular tetrahedron is therefore only one member of the three-dimensional equality family. Any body between the two sets in (5.2) is also an extremizer.

This has a direct consequence for stability. Near equality should force proximity to the common extremal ellipsoid and contact family. It cannot force every body to be close to a unique simplex.

## 6. Quantitative stability near equality

The deficit identity provides the qualitative equality argument almost immediately. Quantitative stability requires estimates that turn its three small terms into distances. We state the geometric estimates first, then combine them with matrix matching.

### 6.1. The geometric estimates needed by the proof

<a id="lem-geometric-control"></a>
**Lemma 6.1 (geometric control).** For the explicit certificate,

```math
\|Q-M_0\|_F^2\le\frac{1-b}{2-b}\chi,\qquad
\sum_i\lambda_i\operatorname{dist}(u_i,\mathcal Z_b)^2
\le\frac{32}{3}\chi.
\tag{6.1}
```

If $\chi\le3/2000$, then $\Delta_{\rm geom}\ge\chi/32$.

**Proof deferred to Sections 9.2–9.3.** Section 9.2 proves the two global
estimates through Lemma 9.2. Section 9.3 proves the local implication through
Lemma 9.3, checks the conversion between the two smallness conditions, and
completes Lemma 6.1.

Even without the small-defect assumption, (4.3) and Lemma 6.1 give
$\sum_i\lambda_i\operatorname{dist}(u_i,\mathcal Z_b)^2\le16000\epsilon$.
Thus the contact geometry is controlled globally, with a better constant near equality.

### 6.2. Shape, center, and contact stability

<a id="thm-stability"></a>
**Theorem 6.2 (dimension-independent stability).** Let $\mathcal E(c,A)$ be any feasible cut ellipsoid in John coordinates, and assume
$0\le\epsilon=\log(R_n/\det A)\le10^{-6}$. Then

```math
\begin{aligned}
\chi&\le32\epsilon,&
\|Q-M_0\|_F&\le4\sqrt\epsilon,\\
\|A-A_*\|_F&\le30\sqrt\epsilon,&
\|c-c_*\|&\le50\sqrt\epsilon,
\end{aligned}
\qquad
\sum_i\lambda_i\operatorname{dist}(u_i,\mathcal Z_b)^2
\le\frac{1024}{3}\epsilon.
\tag{6.2}
```

The constants are independent of $n$. The threshold $10^{-6}$ is a sufficient
condition for entering the local regime of Lemma 6.1; the proof below shows
this implication explicitly. The numbers $30$ and $50$ are convenient upper
bounds obtained when the shape and center estimates are combined.

The proof below uses Lemma 6.1, whose proof is deferred as stated above.
The polar-factor and support-mismatch estimates used in the shape and center
steps are established in Section 9.4.

**Proof.** We pass from the contact defect to the certificate, then to the shape and center.

**Contact geometry.** First use the global bound to enter the small-defect
regime, then use the stronger local bound. This is the purpose of the
threshold on $\epsilon$. By (4.3) and Lemma 6.1,

```math
\chi\le1500\epsilon\le\frac3{2000}
\quad\Longrightarrow\quad
\chi\le32\Delta_{\rm geom}\le32\epsilon.
\tag{6.3}
```

Consequently,

```math
\|Q-M_0\|_F^2\le\frac{1-b}{2-b}\chi\le\frac\chi2\le16\epsilon,
\qquad
\sum_i\lambda_i\operatorname{dist}(u_i,\mathcal Z_b)^2
\le\frac{32}{3}\chi\le\frac{1024}{3}\epsilon.
\tag{6.4}
```

**Shape.** There are two errors to combine: matrix matching controls $A$ relative
to $M^{-1}$, and the geometric estimate controls $M^{-1}$ relative to
$A_*=M_0^{-1}$. Set $Y=M^{1/2}AM^{1/2}$.
Then $G\le\epsilon$ and Lemma 4.2 gives $\|Y-I\|_F\le2\sqrt\epsilon$. Section 9.4 establishes
$\lambda_{\min}(M),\lambda_{\min}(M_0)>7/10$ and
$\|M-M_0\|_F\le12\sqrt\epsilon$. Using $A_*=M_0^{-1}$,

```math
\begin{aligned}
\|A-A_*\|_F
&\le\|M^{-1/2}(Y-I)M^{-1/2}\|_F
+\|M^{-1}(M_0-M)M_0^{-1}\|_F\\
&\le\frac{\|Y-I\|_F}{\lambda_{\min}(M)}
+\frac{\|M-M_0\|_F}{\lambda_{\min}(M)\lambda_{\min}(M_0)}\\
&\le\left(\frac{20}{7}+\frac{1200}{49}\right)\sqrt\epsilon
\le30\sqrt\epsilon.
\end{aligned}
\tag{6.5}
```

The inverse-difference identity preserves the multiplication order and requires no commutativity.

**Center.** Recover the displacement from its projections on the contact
normals. Each projection has three contributions: support slack, mismatch
between the contact height and the equality model, and the shape error already
bounded above. Let $r_i=1-c^Tu_i-\|Au_i\|\ge0$. Since
$\gamma_i\ge\alpha_i r_i$ and $\alpha_i\ge\lambda_i/4$,

```math
\sum_i\lambda_i r_i\le4\sum_i\alpha_i r_i\le4\mathcal C\le4\epsilon.
\tag{6.6}
```

The function $g_*(s)=\|A_*u\|-1-s/2$, for $u^Tv=s$, measures the model's
support mismatch at that contact height. It vanishes at the equality contacts.
Section 9.4 proves
$\sum_i\lambda_i g_*(s_i)^2\le8\chi$. Subtracting support values and using isotropy gives

```math
\begin{aligned}
c-c_*={}&-\sum_i\lambda_i r_i u_i
-\sum_i\lambda_i g_*(s_i)u_i\\
&+\sum_i\lambda_i\bigl(\|A_*u_i\|-\|Au_i\|\bigr)u_i.
\end{aligned}
\tag{6.7}
```

For any scalars $a_i$, the frame Bessel inequality is
$\|\sum_i\lambda_i a_i u_i\|^2\le\sum_i\lambda_i a_i^2$.
Moreover,

```math
\sum_i\lambda_i\bigl|\|A_*u_i\|-\|Au_i\|\bigr|^2
\le\sum_i\lambda_i\|(A_*-A)u_i\|^2=\|A_*-A\|_F^2.
\tag{6.8}
```

The triangle and Bessel inequalities now yield

```math
\|c-c_*\|\le4\epsilon+\|A-A_*\|_F+\sqrt{8\chi}
\le50\sqrt\epsilon.
\tag{6.9}
```

This proves all estimates in (6.2). ∎

The conclusion applies to every nearly extremal feasible ellipsoid, including the optimizer. Its geometric interpretation is that a small logarithmic volume deficit forces a square-root scale error in the shape and center. The contact estimate is weighted, so it does not control a single contact whose John weight is arbitrarily small. All distances are measured after John normalization, and no whole-body distance to a unique extremizer is asserted.

## 7. Iteration, rounding, and computation

The two geometric threads also clarify what the result contributes to a cutting-plane method. The contraction theorem gives an exact potential decrease. The certificate gives an instance-dependent bound and a stopping criterion for an ellipsoid subproblem. Rounding supplies a controlled coordinate system for subsequent computations.

### 7.1. The exact-center iteration bound

<a id="cor-iteration"></a>
**Corollary 7.1 (successive exact central cuts).** Suppose
$K_{j+1}=K_j\cap H_j$, where each cutting hyperplane passes through $c(K_j)$. Then

```math
w(K_k)\le R_n^k w(K_0).
\tag{7.1}
```

If $K_0$ is contained in a ball of radius $R$ and all retained regions contain a target ball of radius $r>0$, then

```math
k\le\frac{n\log(R/r)}{-\log R_n}.
\tag{7.2}
```

**Proof.** Iterate the contraction, then compare the resulting upper bound
with the positive volume that the retained target ball requires.
Induction using Theorem 3.1 gives (7.1). Monotonicity of $w$ and the two ball inclusions imply

```math
\kappa_n r^n\le w(K_k)\le R_n^k w(K_0)\le R_n^k\kappa_n R^n.
\tag{7.3}
```

Since $\kappa_n>0$ and $0<R_n<1$,

```math
n\log r\le k\log R_n+n\log R
\quad\Longrightarrow\quad
k(-\log R_n)\le n\log(R/r),
\tag{7.4}
```

which is (7.2). ∎

The product bound treats successive cuts separately. A natural direction is to investigate whether compatibility of near-equality geometries across recentering yields a sharper bound for consecutive cuts.

Thus an oracle process satisfying the retained-ball assumption cannot continue producing such cuts beyond this bound. For minimization, an appropriate objective-sublevel inradius must be established before turning (7.2) into an objective-accuracy guarantee. This qualification is the same one that enters other volume-based localization analyses.

The exact constant improves the finite-dimensional coefficient, while preserving the known $O(n\log(R/r))$ order of the inscribed-ellipsoid method. Its dimension dependence is explicit:

```math
-\log R_n=\log2-\frac12+
\sum_{j=1}^{\infty}\frac1{2j(j+1)n^j}
=\log2-\frac12+\frac1{4n}+\frac1{12n^2}+\frac1{24n^3}+O(n^{-4}).
\tag{7.5}
```

For $n\ge2$, the absolutely convergent logarithmic series gives

```math
\begin{aligned}
-\log R_n
&=\log2+\frac{n-1}{2}\log(1-1/n)\\
&=\log2-\frac12
+\sum_{j\ge1}\left(\frac1{2j}-\frac1{2(j+1)}\right)n^{-j}.
\end{aligned}
\tag{7.6}
```

This proves (7.5); its positive series terms decrease with $n$, so $R_n\uparrow\sqrt e/2$. Together with $R_1<R_2$, the monotonicity holds in every positive dimension.

### 7.2. Rounding also helps initialize the next subproblem

The inclusion (1.2) makes the value of computing a John ellipsoid broader than center selection. In its coordinates, $B_2^n\subseteq K\subseteq nB_2^n$, so both a feasible inner ball and a controlled outer radius are available.

After a central cut, the ball with center $-v/4$ and radius $1/8$ remains feasible. Translating and scaling therefore give the explicit bound

```math
B_2^n\subseteq 8\bigl((K\cap H_v)+v/4\bigr)
\subseteq(8n+2)B_2^n.
\tag{7.7}
```

For $\|z\|\le1$, the point $x=-v/4+z/8$ satisfies

```math
\|x\|\le\frac38<1,\qquad v^Tx\le-\frac14+\frac18=-\frac18<0,
\tag{7.8}
```

proving the first inclusion. For $x\in K\cap H_v$, the rounding bound gives
$\|8(x+v/4)\|\le8\|x\|+2\le8n+2$, proving the second.
Thus an exact John normalization supplies an explicit next-subproblem initialization with radius ratio $O(n)$. For repeated computation, natural extensions include feasible warm starts and certified cuts through approximate centers.

### 7.3. Computable bounds for individual instances

The universal theorem bounds the worst case. A particular instance can admit a stronger certificate. One may fix the balanced weights in (3.5) and optimize only the vector multipliers, or optimize all multipliers in the normalized dual. The explicit certificate is feasible for both choices, so such optimization can only improve its determinant bound.

For any polytope ellipsoid subproblem, a primal–dual feasible pair with gap $G$ satisfies

```math
\operatorname{vol}\mathcal E(c,A)\ge e^{-G}w(\mathcal P).
\tag{7.9}
```

Indeed, with $p_*:=\log(w(\mathcal P)/\kappa_n)$, weak duality gives

```math
p_*\le-\log\det M=\log\det A+G
\quad\Longrightarrow\quad
\frac{\operatorname{vol}\mathcal E(c,A)}{w(\mathcal P)}
=e^{\log\det A-p_*}\ge e^{-G}.
\tag{7.10}
```

This is a relative-volume stopping criterion for a primal–dual feasible computation. Relating this gap to center error could lead to certified contraction guarantees for cuts through computed centers.

For a fixed John frame and cut direction, let $\mathfrak D(\mathcal U,v)$ denote the maximum determinant in the normalized dual. Exact duality and the contact reduction give

```math
\frac{w(P_{\mathcal U}\cap H_v)}{\kappa_n}
=\mathfrak D(\mathcal U,v)^{-1},\qquad
C_n=\left(\inf_{\mathcal U,v}\mathfrak D(\mathcal U,v)\right)^{-1},
\qquad \inf_{\mathcal U,v}\mathfrak D(\mathcal U,v)=R_n^{-1}.
\tag{7.11}
```

The last infimum is attained by the equality models. Exact duality and
contact recovery were proved in Section 2.3. Section 10 discusses further
properties of the certificate and related matrix inequalities.

## 8. Proof of Theorem 3.2: the John-frame certificate bound

We now prove Theorem 3.2, deferred in Section 3.3. After normalization,
its determinant assertion is Theorem 8.1 below. Section 8.6 will return to
the original certificate and complete both statements.

First normalize the determinant at the equality model. Section 8.1 records
the scalar moments needed for the high-dimensional proof in Section 8.2.
Only after that proof do we introduce transverse blocks: Section 8.3 gives
their basic constraints and settles dimension two. Section 8.4 states and
proves the direct coupling estimate used in dimension three and local
stability, followed by the three-dimensional proof in Section 8.5.
Section 8.6 combines the branches and recovers equality.

**From the certificate to a symmetric matrix.** Recall $b=1/n$,
$P=I-vv^T$, and $u_i=s_iv+y_i$, where $s_i=u_i^Tv$ and $y_i=Pu_i$.
Use the parameters of Section 3:
$d=2-b$, $a=b/d$, $t=(1+b)/2$, $k=2\sqrt{1-b}/d$, and
$f(s)=(1-ts)/(1-as)$. These parameters depend only on the dimension; the
contact data enter through the weighted second-moment matrix $B$ below.
The useful factorization of the existing certificate is

```math
\begin{aligned}
B&=\sum_i\lambda_i f(s_i)u_iu_i^T,&
F&=B+\frac{t}{1-a}vv^T,\\
D&=kP+k^2vv^T,&Q&=FD.
\end{aligned}
\tag{8.1}
```

Here $F$ adds a rank-one axial term to $B$, while $D$ rescales the transverse
directions by $k$ and the axial direction by $k^2$. This separates the
frame-dependent symmetric matrix $F$ from a fixed scaling whose determinant
is known.

To check the factorization, use
$\sum_i\lambda_i f(s_i)u_i=aBv-tv$ in the expansion of (3.11).
It gives $Q=BD+t(1+a)vv^T=FD$. All $f(s_i)$ are positive, so isotropy
makes $B$ and $F$ positive definite. Also $D\succ0$. This already proves
that $Q$ is invertible and has positive determinant.

**Choose the equality model as the reference.** At the model contacts, the
certificate is $Q=M_0=A_*^{-1}$. Thus the corresponding symmetric factor is
$F_0=M_0D^{-1}$. Normalize $F$ by this reference matrix:

```math
\begin{gathered}
F_0=\frac{d^2}{2(1-b)}vv^T+\frac d2P,
\qquad\widehat F=F_0^{-1/2}FF_0^{-1/2},\\
F_0D=M_0,\qquad\det\widehat F=R_n\det Q.
\end{gathered}
\tag{8.2}
```

This congruence preserves positive definiteness and sends $F_0$ to the identity.
Consequently, $\widehat F-I$ measures the matrix departure from the equality
model. The last identity uses $\det D=k^{n+1}$ and
$\det(F_0D)=\det M_0=R_n^{-1}$. Thus the normalized determinant theorem
below is exactly the quantitative assertion needed in Theorem 3.2.

To measure the same departure directly in the contact data, recall the scalar
defect from (3.10):

```math
\chi=\sum_i\lambda_i\frac{(1+s_i)(s_i-b)^2}{1-as_i}\ge0.
\tag{8.3}
```

The factors $1+s_i$ and $(s_i-b)^2$ make each summand vanish at the model pole
and latitude, respectively. The denominator is positive, and the John weights
retain the contribution of each contact. The next theorem links this scalar
description of contact geometry to the normalized determinant.

<a id="thm-determinant"></a>
**Theorem 8.1 (quantitative John-frame determinant inequality).** Every John frame in dimension $n\ge2$ satisfies

```math
\frac{\chi}{1500}\le\log\det\widehat F\le\frac{\chi}{2d},
\qquad
\det F\ge\det F_0=\frac{d^{n+1}}{2^n(1-b)}.
\tag{8.4}
```

Equality in the determinant inequality holds if and only if $s_i\in\{-1,b\}$ for every contact, in which case $F=F_0$ and $\widehat F=I$.

**Proof developed in Sections 8.1–8.6.** The dimension-specific lower
bounds are established in Sections 8.2, 8.3, and 8.5; Section 8.6 assembles
them and proves the upper bound and equality statement.

The upper estimate will follow from the trace of $\widehat F-I$. The main work
is the lower estimate: a positive trace alone does not give the required determinant lower bound,
so we must use the relations between the matrix entries imposed by the contacts.
The coefficient $1/1500$ is the explicit margin produced by these estimates.
The sharp geometric constant is $R_n$; the proof does not assert optimality
of this quantitative margin.

### 8.1. Scalar preparation for Theorem 8.1

For the high-dimensional argument, the needed contact information is the
height $s_i$ and the scalar defect $\chi$. Reweight by
$\nu_i=\lambda_i/(1-as_i)$ to absorb the denominator in $f$, and write
$N_r=\sum_i\nu_i s_i^r$. The scalar John moments give

```math
N_0-aN_1=n,\qquad N_1-aN_2=0,\qquad N_2-aN_3=1.
\tag{8.5}
```

The three relations express $N_0,N_1,N_3$ in terms of $N_2$.
Expanding the defect gives

```math
\chi=N_3+(1-2b)N_2+(b^2-2b)N_1+b^2N_0.
\tag{8.6}
```

Substitution expresses the axial entry of $B$ as

```math
\zeta:=v^TBv=N_2-tN_3
=\frac{3d}{4}-\frac{d^2}{4(1-b)(2+b)}\chi.
\tag{8.7}
```

This is the scalar input used below: departure from the model lowers
$\zeta$ by a known multiple of $\chi$. All denominators are positive since
$0<b\le1/2$ and $-1\le s_i\le1$. The transverse information will be introduced
when the low-dimensional argument needs it.

### 8.2. Higher dimensions in Theorem 8.1

We now prove the lower bound in Theorem 8.1 for $n\ge4$, so $0<b\le1/4$.
Two lemmas isolate the quantities to compare: Lemma 8.2 gives a determinant
gain and leaves a scalar logarithmic difference; Lemma 8.3 bounds that
difference. Lemma 8.4 then completes the constant comparison.

#### 8.2.1. The lifted determinant bound

Set $\ell(s)=\log f(s)$ and $\widetilde u_i=(u_i,\sqrt b)$.
Define the lifted moment matrix and weighted logarithmic sum by

```math
\mathcal A=\sum_i\lambda_i f(s_i)\widetilde u_i\widetilde u_i^T,
\qquad \mathcal L=\sum_i\lambda_i\log f(s_i).
\tag{8.8}
```

The corresponding value for the pole-and-latitude model is

```math
\mathcal L_0:=\frac{\ell(-1)}{1+b}+\frac{\ell(b)}{b(1+b)}.
\tag{8.9}
```

The two coefficients are the total John weights at the model pole and latitude.
Define also the gain coefficient

```math
\delta_0(b):=\frac{(1+b)(b^2+b+2)}
{2d(1-b)(2+b)(3+b)}.
\tag{8.10}
```

<a id="lem-lifted-bound"></a>
**Lemma 8.2 (lifted determinant bound).** For every John frame in dimension
$n\ge4$,

```math
\log\det\widehat F
\ge (1+b)(\mathcal L-\mathcal L_0)+\delta_0(b)\chi.
\tag{8.11}
```

The matrix problem is thus reduced to a lower bound on
$\mathcal L-\mathcal L_0$. The next subsection estimates precisely this term.

**Proof. Encode the moments in the lifted matrix.** The constant last
coordinate turns the zero first moment into zero off-diagonal blocks, and
$b=1/n$ makes the final diagonal entry equal to one.

John's first and second moments combine into $\sum_i\lambda_i\widetilde u_i\widetilde u_i^T=I_{n+1}$. We use the standard finite-frame determinant estimate

```math
XX^T=I_r,\quad \rho_i>0
\quad\Longrightarrow\quad
\log\det\bigl(X\operatorname{diag}(\rho_i)X^T\bigr)
\ge\sum_i\|X_i\|^2\log\rho_i,
\tag{8.12}
```

where $X_i$ are the columns. The point of this estimate is to replace a matrix
determinant by a weighted scalar sum. In the standard Cauchy–Binet/Jensen
argument [HJ1985; BV2004], the coefficients $w_S=(\det X_S)^2$, for subsets
$S$ of $r$ column indices, form a probability distribution. The needed
determinant identities are

```math
\sum_S w_S=1,\qquad
\det(X\operatorname{diag}(\rho_i)X^T)=\sum_Sw_S\prod_{i\in S}\rho_i,
\qquad \sum_{S\ni i}w_S=\|X_i\|^2.
\tag{8.13}
```

For the marginal identity, expand the same determinant when only the $i$th diagonal weight is $1+z$:
$\det(I_r+zX_iX_i^T)=1+z\|X_i\|^2$.
Comparing coefficients of $z$ suffices. Scalar Jensen now gives

```math
\log\!\left(\sum_Sw_S\prod_{i\in S}\rho_i\right)
\ge\sum_Sw_S\sum_{i\in S}\log\rho_i
=\sum_i\|X_i\|^2\log\rho_i,
\tag{8.14}
```

which proves (8.12). For $X_i=\sqrt{\lambda_i}\widetilde u_i$, this becomes

```math
\log\det\mathcal A\ge(1+b)\mathcal L.
\tag{8.15}
```

**Return to the original determinant.** Both $\mathcal A$ and $F$ contain
$B$, so their determinant ratio can cancel this common matrix factor.
Write $\kappa=t/(1-a)$ for the axial coefficient already present in $F$,
and $\varrho=v^TB^{-1}v$ for the inverse axial moment introduced by the
Schur complement. The same moment identities used in (8.1) give

```math
\mathcal A=
\begin{pmatrix}
B&\sqrt b(aBv-tv)\\
\sqrt b(aBv-tv)^T&1-abt+a^2b\zeta
\end{pmatrix},
\qquad
\det\mathcal A=\frac{\det B}{n}(n+at-t^2\varrho).
\tag{8.16}
```

The Schur complement is positive. The abbreviation $H_0=n+at$ records its
constant part. Our aim is to remove $\varrho$ in favor of the direct axial
moment $\zeta=v^TBv$, whose dependence on $\chi$ is known from (8.7).
The determinant lemma and Cauchy–Schwarz give

```math
\det Q=k^{n+1}\det B(1+\kappa\varrho),\qquad
\varrho\zeta\ge1,\qquad H_0-t^2\varrho>0.
\tag{8.17}
```

Cross multiplication, with positive denominators, therefore yields

```math
\frac{\det Q}{\det\mathcal A}
=nk^{n+1}\frac{1+\kappa\varrho}{H_0-t^2\varrho}
\ge nk^{n+1}\frac{\zeta+\kappa}{H_0\zeta-t^2}.
\tag{8.18}
```

Taking logarithms and applying (8.15), we obtain

```math
\log\det Q\ge(n+1)\log k+(1+b)\mathcal L+g(\zeta),
\quad
g(\zeta)=\log\frac{n(\zeta+\kappa)}{(n+at)\zeta-t^2}.
\tag{8.19}
```

All quantities inside the logarithm are positive: (8.16) gives
$n+at>t^2\varrho\ge t^2/\zeta$.

**Extract the positive gain from the axial correction.** As $\chi$ increases,
(8.7) makes $\zeta$ decrease from its model value $\zeta_0=3d/4$.
The variables $\theta_1,\theta_2$ below measure the relative decreases in the
numerator and denominator inside $g$. The denominator decreases more, which
increases their ratio. The elementary inequality $\log x\ge1-1/x$ will quantify
this increase. Write

```math
\Delta_\zeta=\zeta_0-\zeta
=\frac{d^2\chi}{4(1-b)(2+b)},\qquad
\theta_1=\frac{\Delta_\zeta}{\zeta_0+\kappa},\qquad
\theta_2=\frac{H_0\Delta_\zeta}{H_0\zeta_0-t^2}.
\tag{8.20}
```

The positive-denominator condition implies $0\le\theta_1\le\theta_2<1$. Hence

```math
\begin{aligned}
g(\zeta)-g(\zeta_0)
&=\log\frac{1-\theta_1}{1-\theta_2}
\ge1-\frac{1-\theta_2}{1-\theta_1}\\
&=\frac{\theta_2-\theta_1}{1-\theta_1}
\ge\theta_2-\theta_1=\delta_0(b)\chi,
\end{aligned}
\tag{8.21}
```

The last equality follows by substituting the parameters into the definition
of $\delta_0(b)$.

**Subtract the model value.** Since $f(-1)=d(3+b)/4$ and $f(b)=d/2$,
the model sum defined in (8.9) satisfies

```math
(n+1)\log k+(1+b)\mathcal L_0+g(\zeta_0)=\log R_n^{-1}.
\tag{8.22}
```

Combine (8.19), (8.21), and (8.22), and use
$\log\det\widehat F=\log R_n+\log\det Q$ from (8.2).
This gives (8.11), completing the proof. ∎

#### 8.2.2. The interpolation loss

Keep $\ell(s)=\log f(s)$ and $\mathcal L=\sum_i\lambda_i\ell(s_i)$.
Recall explicitly the model value
$\mathcal L_0=\ell(-1)/(1+b)+\ell(b)/[b(1+b)]$ from (8.9).
Define the scalar integral

```math
I(b):=\int_a^t\frac{z^2}{(1-z^2)(1-bz)^2}\,dz.
\tag{8.23}
```

<a id="lem-hermite"></a>
**Lemma 8.3 (interpolation loss).** With these definitions, every John frame
in dimension $n\ge4$ satisfies

```math
\mathcal L-\mathcal L_0\ge-(1-a)I(b)\chi.
\tag{8.24}
```

This is the scalar estimate needed in Lemma 8.2. Its proof also gives the
exact pointwise remainder (8.27).

**Proof. Choose a quadratic with the correct weighted sum.**
The John identities determine
the weighted average of every quadratic polynomial in the heights. We therefore
replace $\ell(s)=\log f(s)$ by a quadratic that matches the equality heights.
Matching the value at $-1$ and both the value and slope at $b$ also gives the
same vanishing factors as the defect $\chi$. Let $H_2$ satisfy
$H_2(-1)=\ell(-1)$, $H_2(b)=\ell(b)$, and $H_2'(b)=\ell'(b)$. Explicitly,

```math
H_2(s)=\ell(b)+\ell'(b)(s-b)
+\frac{\ell(-1)-\ell(b)+(1+b)\ell'(b)}{(1+b)^2}(s-b)^2.
\tag{8.25}
```

The scalar John moments agree with those of masses $1/(1+b)$ at $-1$ and $1/[b(1+b)]$ at $b$. Since $H_2$ is quadratic,

```math
\sum_i\lambda_iH_2(s_i)=\mathcal L_0.
\tag{8.26}
```

Therefore $\mathcal L-\mathcal L_0$ is the weighted sum of the remainders
$\ell(s_i)-H_2(s_i)$. We will establish the exact identity, for $-1\le s\le1$,

```math
\ell(s)-H_2(s)=-(1+s)(s-b)^2
\int_a^t\frac{z^2\,dz}{(1+z)(1-bz)^2(1-zs)}.
\tag{8.27}
```

**Derive and bound the remainder.** We first prove a rational interpolation identity, then integrate
it to recover the logarithm. This exposes the sign and the vanishing factors
of the remainder explicitly.

**Interpolate the rational integrand.** Put $r_z(s)=s/(1-zs)$ and let
$H_{2,z}$ be the quadratic formula (8.25) with data $r_z(-1)$, $r_z(b)$
and slope $(1-zb)^{-2}$. Clearing denominators gives the exact rational identity

```math
r_z(s)-H_{2,z}(s)
=\frac{z^2(1+s)(s-b)^2}{(1+z)(1-bz)^2(1-zs)}.
\tag{8.28}
```

**Recover the logarithmic interpolant.** The value data integrate to
$\ell(-1)$ and $\ell(b)$ because $\ell(s)=-\int_a^t r_z(s)\,dz$.
It remains to check the slope data; these satisfy the elementary identity

```math
-\int_a^t\frac{dz}{(1-bz)^2}
=-\frac{t-a}{(1-ab)(1-tb)}
=\frac{a}{1-ab}-\frac{t}{1-tb}=\ell'(b).
\tag{8.29}
```

Integration of the three polynomial coefficients therefore gives (8.27), with
no differentiation under the integral. All integrands are continuous and all
denominators are positive on the compact interval.

**Express the loss in units of the contact defect.** To sum the remainder,
we need a coefficient independent of the individual height $s$. The following
comparison leaves the factor defining $\chi$ outside the integral:

```math
\frac{1-a}{1-z}-\frac{1-as}{1-zs}
=\frac{(z-a)(1-s)}{(1-z)(1-zs)}\ge0
\qquad(a\le z\le t,\ -1\le s\le1).
\tag{8.30}
```

It follows pointwise that
$\ell(s)-H_2(s)\ge-(1-a)I(b)(1+s)(s-b)^2/(1-as)$.
Summing with weights $\lambda_i$ proves (8.24). ∎

**Combine the gain and loss estimates.** Lemmas 8.2 and 8.3 now give the
two inputs to the higher-dimensional part of Theorem 8.1. Substituting the
interpolation bound into (8.11) yields

```math
\log\det\widehat F\ge\delta_0(b)[1-\mathcal R(b)]\chi,
\qquad
\mathcal R(b)=\frac{4(1-b)^2(2+b)(3+b)}{b^2+b+2}I(b).
\tag{8.31}
```

Here $\mathcal R(b)=(1+b)(1-a)I(b)/\delta_0(b)$ is the loss as a fraction of
the gain. The remaining task is the scalar comparison in Lemma 8.4.

#### 8.2.3. Exact evaluation and the scalar certificate

The matrix argument is now complete except for a scalar comparison:
$\mathcal R(b)$ measures the interpolation loss as a fraction of the gain
$\delta_0(b)\chi$. We need a uniform margin below one and a positive lower bound
for $\delta_0$. The convenient targets below give
$(1/12)(1-124/125)=1/1500$, the coefficient in Theorem 8.1.

<a id="lem-rational"></a>
**Lemma 8.4 (uniform scalar certificate).** For $0<b\le1/4$,
$\mathcal R(b)<124/125$ and $\delta_0(b)\ge1/12$.

**Proof.** We first reduce to the endpoint $b=1/4$, evaluate the integral by
partial fractions, and compare its exact value with $124/125$.
The lower bound for $\delta_0$ is a separate polynomial comparison at the end.

**Step 1: reduce to the largest parameter.** In the original integral, both
endpoints and the integrand depend on $b$. The substitution
$w=(z-a)/(1-az)$ fixes the lower endpoint at zero and exposes three factors
that can each be compared as $b$ varies:

```math
\mathcal R(b)=\frac{4(2+b)(3+b)}{b^2+b+2}
\int_0^{(2+b)/(4+b)}\frac1{1-w^2}
\left(\frac{2w+b(1-w)}{2+b(1-w)}\right)^2dw.
\tag{8.32}
```

Temporarily name the outside prefactor $\pi$, the rational factor inside the
integrand $\psi_b$, and the upper endpoint $\ell_b$:
$\pi(b)=4(2+b)(3+b)/(b^2+b+2)$,
$\psi_b(w)=[2w+b(1-w)]/[2+b(1-w)]$, and
$\ell_b=(2+b)/(4+b)$. The largest endpoint is $\ell_{1/4}=9/17$.
For $0\le b_1\le b_2\le1/4$ and $0\le w\le9/17$,

```math
\begin{aligned}
\pi(b_2)-\pi(b_1)
&=\frac{16(b_2-b_1)(1-b_1-b_2-b_1b_2)}
{(b_1^2+b_1+2)(b_2^2+b_2+2)}\ge0,\\
\psi_{b_2}(w)-\psi_{b_1}(w)
&=\frac{2(b_2-b_1)(1-w)^2}
{[2+b_1(1-w)][2+b_2(1-w)]}\ge0,\\
\ell_{b_2}-\ell_{b_1}
&=\frac{2(b_2-b_1)}{(4+b_1)(4+b_2)}\ge0.
\end{aligned}
\tag{8.33}
```

Here $1-b_1-b_2-b_1b_2\ge7/16$ and $\psi_b(w)\ge0$. The integrand and interval in (8.32) are therefore increasing in $b$, giving
$\mathcal R(b)\le\mathcal R(1/4)$.

**Step 2: evaluate the endpoint integral by partial fractions.**
Specializing the same $w$-integral (8.32) to $b=1/4$ gives

```math
\mathcal R(1/4)=\frac{468}{37}
\int_0^{9/17}\frac{(1+7w)^2}{(1-w^2)(9-w)^2}\,dw.
\tag{8.34}
```

Its integrand has the elementary decomposition

```math
\begin{aligned}
\frac{(1+7w)^2}{(1-w^2)(9-w)^2}
&=\frac{9}{50(1+w)}+\frac{1}{2(1-w)}\\
&\quad-\frac{8}{25(9-w)}-\frac{256}{5(9-w)^2}.
\end{aligned}
\tag{8.35}
```

All logarithm arguments are positive on $0\le w\le9/17$.
Integrating the four terms and collecting the endpoint logarithms yields

```math
\begin{aligned}
\mathcal R(1/4)
&=\frac{468}{37}
\left(\frac9{50}\log13-\frac1{25}\log2-\frac{16}{45}\right)\\
&=\frac{2106\log13-468\log2-4160}{925}<\frac{124}{125}.
\end{aligned}
\tag{8.36}
```

Together with Step 1, this proves $1-\mathcal R(b)>1/125$ throughout the
required interval.

**Step 3: bound the gain coefficient.** We now check the other input to (8.31).
Clearing the positive denominators in $\delta_0(b)\ge1/12$ gives

```math
6(1+b)(b^2+b+2)-d(1-b)(2+b)(3+b)
=b(26+19b+4b^2-b^3)\ge0.
\tag{8.37}
```

This proves both assertions. ∎

**Higher-dimensional part of Theorem 8.1 completed.** Combining (8.31) with
Lemma 8.4 gives $\log\det\widehat F\ge\chi/1500$ for $n\ge4$.
The remaining dimensions follow below; the common upper bound and equality
statement are completed in Section 8.6.

**Why dimensions two and three require another estimate.** The scalar formula for
$\mathcal R(b)$ is well defined for $0<b\le1/2$. The preceding bound needs
$\mathcal R(b)<1$; for $n=3$ and $n=2$, however, this scalar remainder exceeds one.
Indeed, on $a\le z\le t$,

```math
\frac1{1-z^2}\ge1+z^2+z^4,\qquad
\frac1{(1-bz)^2}\ge1+2bz+3b^2z^2.
\tag{8.38}
```

These follow by multiplying the positive denominators: the two products are
$1-z^6\le1$ and $1-(bz)^3(4-3bz)\le1$. With
$p(b)=4(1-b)^2(2+b)(3+b)/(b^2+b+2)$, exact polynomial integration gives

```math
\begin{aligned}
\mathcal R(b)&\ge p(b)\int_a^t
z^2(1+z^2+z^4)(1+2bz+3b^2z^2)\,dz,\\
\mathcal R(1/3)&>\frac{16}{15}>1,\\
\mathcal R(1/2)&>\frac76>1.
\end{aligned}
\tag{8.39}
```

Thus the scalar estimate does not prove a positive determinant deficit in these
two dimensions. We now retain transverse block information, first to settle
dimension two and then to derive the additional control needed in dimension three.

### 8.3. Block constraints and dimension two in Theorem 8.1

The scalar estimate has reached its limitation. To handle the remaining
dimensions, we retain the components of $u_i=s_iv+y_i$ transverse to $v$.
Work in $\mathbb Rv\oplus v^\perp$, with $m=n-1$.
In the normalized certificate, $x$ measures the axial decrease, $E$ is the
transverse perturbation, and $j$ couples the two subspaces.

<a id="lem-moments"></a>
**Lemma 8.5 (block identities and constraints).** The normalized matrix satisfies

```math
\widehat F=\begin{pmatrix}1-x&j^T\\j&I_m+E\end{pmatrix},
\quad x=\frac{\chi}{2(2+b)},\quad
\sigma:=\operatorname{tr}E=\frac{2\chi}{d(2+b)},\quad x=\frac d4\sigma,
\tag{8.40}
```

where

```math
E=-\frac1d\sum_i\nu_i(s_i-b)y_i y_i^T,
\qquad
j=-\frac{\sqrt{1-b}}{b\sqrt d}\sum_i\nu_i(s_i-b)y_i.
\tag{8.41}
```

The scalar and matrix constraints are

```math
0\le\sigma\le\frac{2(1-b)}{d+b^2},\qquad 0\le\chi\le2,
\tag{8.42}
```

```math
\begin{pmatrix}x&-j^T\\-j&tI_m-E\end{pmatrix}\succeq0,
\qquad -\frac12I_m\prec E\prec tI_m.
\tag{8.43}
```

The trace of $E$ is nonnegative, but $E$ need not be positive semidefinite.
The Gram constraint limits the coupling: for every transverse vector $q$,
$(q^Tj)^2\le x\,q^T(tI_m-E)q$. At the equality contacts, either $y_i=0$
or $s_i-b=0$, so $E=j=0$.

**Proof. Recover the blocks.** The projected John identities are
$\sum_i\lambda_i y_i=\sum_i\lambda_i s_i y_i=0$ and
$\sum_i\lambda_i y_iy_i^T=I_m$. With the reweighted vector and matrix moments
$C_r=\sum_i\nu_i s_i^r y_i$ and $Y_r=\sum_i\nu_i s_i^r y_iy_i^T$, they give

```math
C_0=aC_1,\qquad C_1=aC_2,\qquad Y_0-aY_1=I_m.
\tag{8.44}
```

The identity $f(s)=d/2-(s-b)/[2(1-as)]$ gives the transverse expression
for $E$, or equivalently $Y_1-bY_0=-dE$.
Adding the axial term $t/(1-a)$ to (8.7) and normalizing by $F_0$ gives
$1-x$. Taking the trace of $E$, using $\|y_i\|^2=1-s_i^2$, gives $\sigma$.
The mixed entry follows from $C_1-tC_2$ and (8.44).
This proves (8.40)–(8.41).

**Bound the scalar range.** It suffices to bound $\chi$.
The nonnegative sum $\sum_i\nu_i(1-s_i)(s_i+b)^2$ expands to
$-N_3+(1-2b)N_2+(2b-b^2)N_1+b^2N_0$.
Combining it with (8.5)–(8.6) cancels the remaining free moment:

```math
\chi+\frac{(1-b)(2+b)^2}{(d+b^2)^2}
\sum_i\nu_i(1-s_i)(s_i+b)^2
=\frac{d(2+b)(1-b)}{d+b^2}.
\tag{8.45}
```

Nonnegativity gives the stated bound on $\sigma$ through (8.40).
The estimate $\chi\le2$ also uses
$2(d+b^2)-d(2+b)(1-b)=b(2+3b-b^2)\ge0$.

**Keep the coupling in a positive block matrix.** The required matrix has
the Gram representation

```math
\begin{pmatrix}x&-j^T\\-j&tI_m-E\end{pmatrix}
=\sum_i\nu_i(1+s_i)r_ir_i^T,\qquad
r_i=\binom{(s_i-b)/\sqrt{2(2+b)}}
{\sqrt{(1-b)(2+b)/(2d)}\,y_i}.
\tag{8.46}
```

Its weights are nonnegative, proving the first part of (8.43).
Solving the two relations for $Y_0,Y_1$ gives

```math
\begin{aligned}
\sum_i\nu_i(1-s_i)y_i y_i^T&=\frac d{2+b}(I_m+2E),\\
\sum_i\nu_i(1+s_i)y_i y_i^T&=\frac{2d}{(1-b)(2+b)}(tI_m-E).
\end{aligned}
\tag{8.47}
```

Both sums are positive definite: the contacts at $s_i=\pm1$ have $y_i=0$,
and all other transverse vectors span $v^\perp$ by the John second moment.
Thus $I_m+2E\succ0$ and $tI_m-E\succ0$, proving the strict spectral bounds. ∎

**Dimension two.** Here $m=1$, so the trace determines the transverse block:
$E=\sigma$, $x=3\sigma/8$, and $t=3/4$.
The remaining coupling loss is $j^2$. Substituting the Gram bound
$j^2\le x(t-\sigma)$ into the determinant gives

```math
\det\widehat F\ge(1-x)(1+\sigma)-x(t-\sigma)
=1+\frac{11}{32}\sigma=1+\frac{11}{60}\chi.
\tag{8.48}
```

Dimension three needs further control because the transverse trace alone no
longer determines the transverse determinant. We next state the precise
estimate needed there.

### 8.4. A direct bound for transverse deformation and coupling

For the two-dimensional transverse block in the next subsection, we need to
control its deformation and its coupling to the axis together. The same
bound will also be used for local stability in Section 9.3.
The matrix $K_E=I_m+2E$ is positive definite by Lemma 8.5.
The nonnegative quantity $A_E=\operatorname{tr}(E^2K_E^{-1})$ measures
transverse deformation: each eigenvalue $e$ of $E$ contributes $e^2/(1+2e)$.

<a id="lem-variational"></a>
**Lemma 8.6 (direct coupling bound).** Let
$K_E=I_m+2E$, $A_E=\operatorname{tr}(E^2K_E^{-1})$, and
$L=d(1-b)/(d+b^2)-d\sigma/2\ge0$.
If $\sigma>0$, then

```math
A_E\le\frac\sigma2,\qquad
\|K_E^{-1}j\|^2\le L\left(\frac\sigma2-A_E\right).
\tag{8.49}
```

The first inequality bounds transverse deformation. The second says that
the remaining amount $\sigma/2-A_E$ controls the transformed coupling.
The coefficient $L$ is the distance to the upper trace bound in
(8.42), multiplied by $d/2$.

**Proof. Evaluate only the tests needed for these conclusions.**
We will take $Z=EK_E^{-1}$, first with $q=0$ and then with
$q=K_E^{-1}j/L$ when $L>0$. For these calculations set

```math
\ell=\operatorname{tr}(ZE)+q^Tj,\qquad
Q_2=\operatorname{tr}(Z^2K_E)+4q^TZj+L\|q\|^2.
\tag{8.50}
```

To bound this expression directly from the frame, put
$\gamma=\sqrt{d(1-b)}/(d+b^2)$. The mixed moments, transverse identity,
and scalar relation in Section 8.3 give, respectively,

```math
\begin{aligned}
\sum_i\nu_i(1-s_i)y_iy_i^T&=\frac d{2+b}K_E,\\
\gamma\sum_i\nu_i(1-s_i)(s_i+b)y_i&=\frac{2d}{2+b}j,\\
\gamma^2\sum_i\nu_i(1-s_i)(s_i+b)^2&=\frac d{2+b}L.
\end{aligned}
\tag{8.51}
```

Together with the expression for $E$, these identities evaluate the linear
form and its associated squared norm:

```math
\begin{aligned}
\ell&=-\frac1d\sum_i\nu_i(s_i-b)y_i^T
       \bigl(Zy_i+\gamma(s_i+b)q\bigr),\\
\sum_i\nu_i(1-s_i)\|Zy_i+\gamma(s_i+b)q\|^2
&=\frac d{2+b}Q_2.
\end{aligned}
\tag{8.52}
```

Weighted Cauchy–Schwarz, with
$\|y_i\|^2=(1-s_i)(1+s_i)$, therefore gives
$\ell^2\le\chi Q_2/[d(2+b)]=(\sigma/2)Q_2$.
Pole terms have $y_i=0$, so this calculation requires no division by
$1\pm s_i$. Completing one scalar square yields

```math
2\ell-Q_2\le2\ell-\frac{2\ell^2}{\sigma}
=\frac\sigma2-\frac2\sigma\left(\ell-\frac\sigma2\right)^2
\le\frac\sigma2.
\tag{8.53}
```

**Extract the deformation and coupling bounds.**
The chosen $Z=EK_E^{-1}$ is symmetric and makes
$\operatorname{tr}(ZE)=\operatorname{tr}(Z^2K_E)=A_E$.
With $q=0$, this gives $2\ell-Q_2=A_E$, proving the first bound.
Keeping this $Z$, use $2EK_E^{-1}=I_m-K_E^{-1}$: the part depending on $q$
is $2q^TK_E^{-1}j-L\|q\|^2$. For $L>0$ it is maximized at the chosen
$q=K_E^{-1}j/L$, giving

```math
2\ell-Q_2=A_E+\frac1L\|K_E^{-1}j\|^2\le\frac\sigma2.
\tag{8.54}
```

If $L=0$, the same finite Cauchy–Schwarz calculation with $Z=0$ and $q=j$
gives $\|j\|^4\le0$, hence $j=0$. This proves the second bound at that endpoint.
The case $\sigma=0$ has $E=j=0$ by (8.40)–(8.41), so the estimates extend
there as well. ∎

The useful output is (8.49). Section 10.4 records the more general inequality
for arbitrary tests; the proof here has already supplied everything needed
for the three-dimensional and local stability arguments.

### 8.5. Dimension three in Theorem 8.1: a single polynomial certificate

The transverse block is now two-dimensional, so its trace no longer determines
its determinant. We must control both the transverse determinant and its
interaction with $j$. The proof first expresses that interaction through two
scalar quadratic forms, then combines the Gram and variational inequalities
to remove them. The remaining task is a polynomial bound on an interval.

<a id="prop-dim3"></a>
**Proposition 8.7 (three-dimensional bound).** In dimension three,

```math
\det\widehat F\ge1+\frac2{11}\sigma
=1+\frac{36}{385}\chi.
\tag{8.55}
```

**Proof.** The desired output is a positive determinant excess proportional
to $\sigma$. The coefficient $2/11$ below is the margin supplied by the
polynomial estimate.

**Step 1: describe the transverse block by scalar invariants.** In dimension
three, the definitions specialize to $E\in\mathbb S^2$, $x=5\sigma/12$,
$t=2/3$, and $0\le\sigma\le3/4$. If $\sigma=0$, the defect vanishes and
(8.41) gives $\widehat F=I$. Suppose $\sigma>0$ and write

```math
p=\det E,\qquad z=\sigma+4p,\qquad
L=\frac58-\frac56\sigma,\qquad
\Delta=\frac{11}{3}(1+\sigma)-z.
\tag{8.56}
```

Here $p$ is the second invariant of $E$ besides its trace. The combination
$z=\sigma+4p$ is chosen because it expresses the variational remainder
$\sigma-2A_E$ by a simple fraction. The coefficient $L$ is exactly the one
in Lemma 8.6 at $n=3$. The quantity $\Delta$ will be the positive denominator
when we combine the two coupling inequalities.
For a two-by-two matrix, Cayley–Hamilton gives

```math
\det K_E=1+\sigma+z,\qquad
\sigma-2A_E=\frac{z}{1+\sigma+z}.
\tag{8.57}
```

Lemma 8.6 and $\det E\le\sigma^2/4$ therefore imply

```math
0\le z\le\sigma(1+\sigma),\qquad
j^TK_E^{-2}j\le\frac{Lz}{2(1+\sigma+z)},\qquad \Delta>0.
\tag{8.58}
```

Thus $z$ lies in an explicit interval once $\sigma$ is fixed. This will later
make a concavity argument possible.

**Step 2: bound exactly the coupling term in the determinant.** For a
two-by-two transverse block, that term is
$j^T\operatorname{adj}(I_2+E)j=(1+\sigma)\|j\|^2-j^TEj$.
Use the short names $r=\|j\|^2$ and $\omega=j^TEj$ for these two quadratic
forms, and set $N=tI_2-E\succ0$. The Gram constraint and (8.58) read, respectively,

```math
(t-\sigma)r+\omega\le x\det N,
\tag{8.59}
```

```math
\bigl[(1+\sigma)(1+4\sigma)-z\bigr]r-4(1+\sigma)\omega
\le\frac L2z(1+\sigma+z).
\tag{8.60}
```

Both inequalities are linear in $r,\omega$. Choose a positive combination
whose coefficients are exactly those of $(1+\sigma)r-\omega$.
Solving this two-variable coefficient-matching problem gives the multipliers
$[3(1+\sigma)+z]/\Delta$ and $5/(3\Delta)$, respectively.
Their positivity preserves the inequality direction, and their common
denominator explains the definition of $\Delta$. Adding yields

```math
j^T\operatorname{adj}(I_2+E)j
\le\frac{x\det N[3(1+\sigma)+z]+\frac56Lz(1+\sigma+z)}\Delta.
\tag{8.61}
```

**Step 3: eliminate the matrix variables.** Substitute this bound into
$\det\widehat F=(1-x)(1+\sigma+p)-j^T\operatorname{adj}(I_2+E)j$
and use $p=(z-\sigma)/4$. Multiplication by $108\Delta$ clears the variable
denominator and gives a polynomial in $\sigma,z$ alone; $108$ is a convenient
positive normalization of its rational coefficients:

```math
108\Delta(\det\widehat F-1)\ge\mathcal P_*(\sigma,z),
\tag{8.62}
```

```math
\mathcal P_*(\sigma,z)=72\sigma(1+\sigma)
+\left(\frac{171}{4}-\frac{53}{4}\sigma+75\sigma^2\right)z
+\left(-\frac{333}{4}+75\sigma\right)z^2.
\tag{8.63}
```

**Step 4: use concavity to check only the endpoints.** The coefficient of
$z^2$ is negative for $0\le\sigma\le3/4$, so the minimum over the admissible
$z$ interval occurs at an endpoint. At $z=0$ the polynomial is
$72\sigma(1+\sigma)$. We show that the other endpoint is at least this large.
At $z=\sigma(1+\sigma)$, it equals

```math
\frac{\sigma(1+\sigma)}4
\bigl(300\sigma^3+267\sigma^2-386\sigma+459\bigr)
\ge72\sigma(1+\sigma),
\tag{8.64}
```

because the cubic in parentheses minus $288$ has the nonnegative decomposition

```math
300\sigma^3+267\left(\sigma-\frac34\right)^2
+\frac{29}{2}\sigma+\frac{333}{16}.
\tag{8.65}
```

Consequently $\mathcal P_*\ge72\sigma(1+\sigma)$ throughout the admissible
interval. Returning through (8.62), the bound
$\Delta\le11(1+\sigma)/3$ cancels $1+\sigma$ and gives
$\det\widehat F-1\ge2\sigma/11$.
Thus $2/11=72/[108(11/3)]$ is the final margin left by the polynomial bound. ∎

Keeping $L=5/8-5\sigma/6$ is decisive: a larger coefficient weakens the second constraint and loses the single-interval polynomial certificate. The proof uses only the moment identities, positive-semidefinite blocks, two-by-two matrix identities, and polynomial inequalities with rational coefficients.

### 8.6. Completion of Theorems 8.1 and 3.2

The three branches now supply determinant excess. We put them on the same
logarithmic scale, then recover the upper bound and the equality condition.

**Obtain one lower bound for all dimensions.**
For $n\ge4$, Lemma 8.4 and (8.31) give $\log\det\widehat F\ge\chi/1500$.
For $n=2,3$, equations (8.48) and (8.55) give $\det\widehat F\ge1+c\chi$ with $c=11/60$ and $c=36/385$, respectively. Since $\chi\le2$ and $\log(1+u)\ge u/(1+u)$ for $u\ge0$,

```math
\log\det\widehat F\ge\frac{c}{1+2c}\chi\ge\frac{\chi}{1500}.
\tag{8.66}
```

**Use the trace for the upper bound.** This part is common to all dimensions:

```math
\log\det\widehat F\le\operatorname{tr}\widehat F-n
=\sigma-x=\frac{\chi}{2d}.
\tag{8.67}
```

**Recover equality from zero defect.** The lower bound forces $\chi=0$ when
$\det\widehat F=1$. Every summand in (8.3) is nonnegative with a positive weight
and denominator, so this is equivalent to $s_i\in\{-1,b\}$ for all $i$.
Conversely, this contact condition gives $x=j=E=0$ by (8.40)–(8.41).
This completes the proof of Theorem 8.1 announced at the start of Section 8.

By (8.2), this proves (3.12). At equality $F=F_0$, hence $Q=M_0$; together with the positivity established above, this completes Theorem 3.2.

## 9. Proof of Lemma 6.1 and supporting estimates for Theorem 6.2

We now supply the proof of Lemma 6.1 deferred in Section 6.1, and the
auxiliary shape and center estimates deferred in the proof of Theorem 6.2.
Sections 9.2–9.3 prove the global and local parts of Lemma 6.1, respectively;
Section 9.4 supplies the remaining inputs to Theorem 6.2. The quantities have
three distinct roles: $\epsilon$ measures the total logarithmic volume deficit,
$\chi$ measures departure of the contacts from the equality set, and
$\sigma=2\chi/[d(2+b)]$ is the same contact defect in the block normalization.
We first turn $\chi$ into matrix and contact-distance bounds. We then improve
the determinant lower bound near equality and transfer the resulting matrix
control to the ellipsoid's shape and center.

The constants record successive sufficient estimates in this chain.
The threshold in Lemma 9.3 ensures that a quadratic logarithm bound applies;
Section 9.4 uses fixed spectral bounds to control inversion. The final
coefficients $30$ and $50$ collect those estimates and are not asserted to
be optimal stability constants.

### 9.1. Complementarity and matrix matching

Use the primal and dual quantities from (4.1)–(4.2). The following identities
also give the weighted multiplier estimate mentioned in Section 4.3.
Here $(\tau,x)$ denotes a generic scalar–vector cone pair; the indexed
$(\tau_r,x_r)$ are the support slack and vector from (4.1).

<a id="prop-gap-control"></a>
**Proposition 9.1 (quantitative complementarity and matrix matching).** For cone-feasible $(\alpha,q)$ and $(\tau,x)$,

```math
2\alpha\tau(\alpha\tau-q^Tx)
=\|\alpha x-\tau q\|^2
+\alpha^2(\tau^2-\|x\|^2)+\tau^2(\alpha^2-\|q\|^2).
\tag{9.1}
```

If $G\le\epsilon\le1/4$, then

```math
\|Y-I\|_F\le2\sqrt\epsilon,\qquad
\sum_{\alpha_r>0}\alpha_r\tau_r
\left\|\frac{x_r}{\tau_r}-\frac{q_r}{\alpha_r}\right\|^2
\le2\epsilon.
\tag{9.2}
```

Here zero-normal redundant inequalities are removed. The first estimate also holds with $Y$ replaced by $A^{1/2}MA^{1/2}$.

**Proof.** The sum-of-squares identity converts a small cone pairing into
closeness of the normalized cone directions. Expanding the squares proves
(9.1), and cone feasibility makes every term on its right nonnegative.
For a nonzero normal, $A\succ0$ and primal feasibility imply
$\tau_r\ge\|Ag_r\|>0$. Divide (9.1) by $\alpha_r\tau_r$ when $\alpha_r>0$
and sum. The total cone gap is at most $\epsilon$, giving the second bound.

The matrix estimate is Lemma 4.2:
$\|Y-I\|_F\le2\sqrt G\le2\sqrt\epsilon$.
The symmetric positive-definite matrices $M^{1/2}AM^{1/2}$ and
$A^{1/2}MA^{1/2}$ have the same eigenvalues, so their Frobenius distances
from the identity agree. This proves the final assertion. ∎

### 9.2. Global part of Lemma 6.1: geometric residuals

We return to the block and contact notation of Section 8. The aim is to make
the scalar defect $\chi$ useful in two ways: as a bound on the certificate's
matrix error, and as a bound on the distance of the contacts from the equality
set. For the matrix bound, we seek a residual for each contact whose squared
norm is proportional to that contact's summand in $\chi$. Isotropy will then
combine these residuals without a dimension factor.

<a id="lem-residual"></a>
**Lemma 9.2 (geometric residual).** For the explicit certificate,

```math
\|Q-M_0\|_F^2\le\frac{1-b}{d}\chi,\qquad
\|\widehat F-I\|_F^2\le\frac\chi d,
\qquad
\sum_i\lambda_i\operatorname{dist}(u_i,\mathcal Z_b)^2
\le\frac{32}{3}\chi.
\tag{9.3}
```

**Proof. Step 1: express the certificate error as contact residuals.**
Subtract the model certificate from $Q$ and use the zero first moment to add
a term that vanishes in the aggregate. This makes the individual residual
vanish at both the pole and the model latitude.
For $u=sv+y$ with $y\perp v$, the resulting residual is

```math
\xi(u)=-\frac{s-b}{d(1-as)}
\bigl[(1-b)(s+1)v+\sqrt{1-b}\,y\bigr].
\tag{9.4}
```

Expansion of $Q-M_0$, followed by the first and second John moments, gives

```math
Q-M_0=\sum_i\lambda_i u_i\xi(u_i)^T,
\qquad
\|\xi(u)\|^2=\frac{1-b}{d}\frac{(1+s)(s-b)^2}{1-as}.
\tag{9.5}
```

For clarity, the axial coefficient before simplification is
$f(s)(s-a)-(2-t)s+b$, and the transverse coefficient is
$kf(s)-\sqrt{1-b}$. The added constant vector $bv$ contributes zero to the aggregate by balance. Their simplification gives (9.4), and orthogonality gives the norm identity.

**Step 2: use isotropy to bound the total matrix error.** The matrix with
columns $\sqrt{\lambda_i}u_i$ has orthonormal rows. Its Bessel inequality
bounds the squared Frobenius norm of the aggregate by the sum of the
weighted squared residuals. Applying this to (9.5) proves the first estimate.
To transfer it to the normalized matrix, use
$Q-M_0=F_0^{1/2}(\widehat F-I)F_0^{1/2}D$.
The product of the least singular values of the two outside factors is
$\sqrt{1-b}$, giving the second estimate. The two matrix constants in (9.3)
thus come from the exact residual identity and the fixed normalization.

**Step 3: compare the scalar residual with geometric distance.**
The equality set consists of a pole and a latitude sphere. We choose an
explicit comparison point in one of these two pieces. It suffices to show

```math
\frac{(1+s)(s-b)^2}{1-as}
\ge\frac3{32}\operatorname{dist}(u,\mathcal Z_b)^2.
\tag{9.6}
```

The split at $s=-1/2$ gives simple uniform bounds in both regions.
If $s\le-1/2$, use the pole, whose squared distance is $2(1+s)$;
then $(s-b)^2\ge1/4$ and $1-as\le4/3$.
If $s\ge-1/2$, choose the point on the latitude with the same transverse
direction, choosing any unit transverse vector if $y=0$. Its squared distance is

```math
(s-b)^2+\bigl(\sqrt{1-s^2}-\sqrt{1-b^2}\bigr)^2\le4(s-b)^2.
\tag{9.7}
```

Indeed, rationalization bounds the squared root difference by
$(s-b)^2(s+b)^2/(1-b^2)\le3(s-b)^2$.
Also $(1+s)/(1-as)\ge3/8$. These two comparisons give the same coefficient
$3/32$ in (9.6); its reciprocal is the contact-distance constant in (9.3).
Summing with the John weights finishes the proof. ∎

**Global part of Lemma 6.1 proved.** The first and third inequalities in
(9.3) are exactly the two estimates in (6.1), since $d=2-b$.
The local implication in Lemma 6.1 remains to be proved in Section 9.3.

**What the global estimates provide.** Combining Theorem 8.1, Proposition 4.1,
and Lemma 9.2 gives

```math
\chi\le1500\epsilon,\qquad
\sum_i\lambda_i\operatorname{dist}(u_i,\mathcal Z_b)^2\le16000\epsilon,
\qquad
\log\det\widehat F\ge\frac1{1000}\|\widehat F-I\|_F^2.
\tag{9.8}
```

### 9.3. Local part of Lemma 6.1: coercivity near equality

The global estimate is enough to place a nearly extremal ellipsoid in a small
neighborhood of the model. Here we improve its coefficient within that
neighborhood. The idea is that the positive linear term
$\operatorname{tr}(\widehat F-I)=\sigma-x$ should exceed the quadratic remainder
in $\log\det\widehat F$. We need to bound the whole perturbation, including
$j$, tightly enough for this difference to remain positive.

The threshold $10^{-3}$ below is a sufficient size condition for that
comparison. The intermediate bounds $1/40$ and $1/30$ specify the small
spectral intervals used in the proof; the useful conclusion is the final
lower bound $\sigma/16$.

<a id="lem-local"></a>
**Lemma 9.3 (local coercivity).** If $\sigma\le10^{-3}$, then

```math
\log\det\widehat F\ge\frac\sigma{16}\ge\frac\chi{32}.
\tag{9.9}
```

**Proof.** If $\sigma=0$, the assertion follows from $\widehat F=I$.
Suppose $\sigma>0$.

**Step 1: confine the transverse eigenvalues.** We first use Lemma 8.6 to
control $E$ and $j$ in the metric determined by $K_E$.
Here $0\le L\le d(1-b)/(d+b^2)<1$ by its definition and
$(d+b^2)-d(1-b)=2b>0$. Lemma 8.6 therefore gives

```math
A_E+\|K_E^{-1}j\|^2\le\frac\sigma2.
\tag{9.10}
```

Every eigenvalue $e>-1/2$ of $E$ therefore satisfies
$e^2/(1+2e)\le1/2000$. This scalar inequality implies $|e|\le1/40$:
the quotient increases as $e$ moves away from zero on either side, and its
values at $\pm1/40$ already exceed $1/2000$.
The choice $1/40$ gives the simple interval $[19/20,21/20]$ for the eigenvalues
of $K_E$. We can now compare the metric in (9.10) with ordinary Frobenius
and Euclidean norms:

```math
\|E\|_F^2+\frac{20}{21}\|j\|^2\le\frac{21}{40}\sigma.
\tag{9.11}
```

**Step 2: control the full perturbation.** Its squared norm contains
$2\|j\|^2$, so the estimate in (9.11) needs one further bound on the coupling.
The Gram constraint gives $\|j\|^2\le x(t+1/40)\le47\sigma/160$.
The coefficient $47/160$ combines $xt\le9\sigma/32$ and
$x/40\le\sigma/80$. Also $x^2\le\sigma/4000$.
Combining these estimates leaves the convenient upper bound $5\sigma/6$:

```math
\|\widehat F-I\|_F^2=x^2+2\|j\|^2+\|E\|_F^2\le\frac56\sigma,
\qquad \|\widehat F-I\|_{\rm op}<\frac1{30}.
\tag{9.12}
```

**Step 3: let the trace gain dominate the logarithmic remainder.**
The size assumption and (9.12) put every eigenvalue perturbation in
$[-1/30,1/30]$. On this interval, integration of the derivative gives
$\log(1+z)\ge z-(15/29)z^2$; the coefficient is
$15/29=1/[2(1-1/30)]$.
The quadratic term is controlled by (9.12), while
$\operatorname{tr}(\widehat F-I)=(1-d/4)\sigma\ge\sigma/2$.
Their difference is

```math
\log\det\widehat F\ge\frac\sigma2-\frac{15}{29}\frac{5\sigma}{6}
=\frac{2\sigma}{29}\ge\frac\sigma{16}.
\tag{9.13}
```

The bound $2\sigma/29$ is rounded down to $\sigma/16$ for subsequent use.
Finally, $\sigma=2\chi/(4-b^2)\ge\chi/2$. ∎

**Completion of the deferred proof of Lemma 6.1.** The first two bounds in Lemma 6.1
are part of Lemma 9.2. Its hypothesis is expressed in $\chi$, while the local
lemma uses $\sigma$, so we check the conversion explicitly. For the small-defect
assertion, $\chi\le3/2000$ implies
$\sigma=2\chi/(4-b^2)\le(8/15)\chi\le1/1250<10^{-3}$.
Lemma 9.3 and (8.2) therefore give $\Delta_{\rm geom}\ge\chi/32$.
This proves the remaining assertion and completes Lemma 6.1, as promised in Section 6.1.

### 9.4. Remaining estimates for Theorem 6.2: shape and center

We now prove the polar-factor and support-mismatch estimates deferred in
Section 6.2. We finish the passage from certificate error to ellipsoid error under the
hypotheses of Theorem 6.2, in particular $\epsilon\le10^{-6}$.
The contact estimate (6.3) already gives $\chi\le32\epsilon$ and hence
$\|Q-M_0\|_F\le4\sqrt\epsilon$. What remains is to transfer this bound through
the polar factor and matrix inversion, then recover the center from support
values. The constants below are explicit bounds for these transfers.

**Step 1: keep the polar factor uniformly invertible.** Set
$\delta=\|Q-M_0\|_{\rm op}\le4\sqrt\epsilon\le0.004$. Since
$M_0=2vv^T+\sqrt{1-b}P$, the triangle inequality gives, for every vector $x$,

```math
\left(\frac1{\sqrt2}-\delta\right)\|x\|
\le\|Q^Tx\|\le(2+\delta)\|x\|,
\qquad
\|Q^Tx\|^2=x^TM^2x.
\tag{9.14}
```

Apply these inequalities to unit eigenvectors of $M\succ0$. Every eigenvalue
lies in $[1/\sqrt2-\delta,\,2+\delta]$.
The rational bounds $7/10$ and $201/100$ lie outside this interval uniformly
under the assumed bound on $\delta$:

```math
\lambda_{\min}(M)>\frac7{10},\qquad
\lambda_{\max}(M)<\frac{201}{100},\qquad
\|Q\|_{\rm op}\le2+\delta<\frac{201}{100}.
\tag{9.15}
```

The lower bound prevents matrix inversion from magnifying small errors
without control. The upper bound will control the product difference in the
next step.

**Step 2: transfer the error from $Q$ to its polar factor.** Since $M^2=QQ^T$,
the difference $X=M-M_0$ satisfies a linear matrix equation. Taking its
Frobenius inner product with $X$ uses the positive spectral lower bounds to
control $\|X\|_F$. The identity $MX+XM_0=QQ^T-M_0^2$ gives

```math
\begin{aligned}
(\lambda_{\min}(M)+\lambda_{\min}(M_0))\|X\|_F^2
&\le\operatorname{tr}(X^TMX)+\operatorname{tr}(X^TXM_0)\\
&=\langle X,QQ^T-M_0^2\rangle_F\\
&\le\|X\|_F\|QQ^T-M_0^2\|_F.
\end{aligned}
\tag{9.16}
```

For $X=0$ the conclusion is immediate; otherwise cancel $\|X\|_F$. Since
$QQ^T-M_0^2=(Q-M_0)Q^T+M_0(Q^T-M_0)$,

```math
\begin{aligned}
\|M-M_0\|_F
&\le\frac{\|QQ^T-M_0^2\|_F}
{\lambda_{\min}(M)+\lambda_{\min}(M_0)}\\
&\le\frac{(\|Q\|_{\rm op}+\|M_0\|_{\rm op})\|Q-M_0\|_F}{7/5}
\le\frac{401}{35}\sqrt\epsilon
\le12\sqrt\epsilon.
\end{aligned}
\tag{9.17}
```

Here $401/35$ is the coefficient obtained by inserting the spectral bounds;
$12$ is a convenient upper bound for it.

**Step 3: transfer the error to the ellipsoid shape.** Matrix matching
controls $A-M^{-1}$, and Step 2 controls $M^{-1}-M_0^{-1}$ using the same
positive lower bounds. The inverse-difference estimate in (6.5) gives

```math
\|A-A_*\|_F
\le\left(\frac{20}{7}+\frac{1200}{49}\right)\sqrt\epsilon
\le30\sqrt\epsilon.
\tag{9.18}
```

The two terms in the coefficient correspond to these two errors, and their
sum is less than $30$. The non-strict conclusion includes $\epsilon=0$.

**Step 4: express the model's support mismatch through the contact defect.**
To recover the center, we need to compare the model support value with the
original supporting plane at each contact. Squaring and subtracting exposes
the pole and latitude factors directly. For a unit vector $u=sv+y$, $y\perp v$,
compute

```math
\|A_*u\|^2-\left(1+\frac s2\right)^2
=\frac{s^2}{4}+\frac{1-s^2}{1-b}-\left(1+\frac s2\right)^2
=\frac{(1+s)(b-s)}{1-b}.
\tag{9.19}
```

Rationalizing therefore gives

```math
g_*(s):=\|A_*u\|-1-\frac s2
=\frac{(1+s)(b-s)}{(1-b)(\|A_*u\|+1+s/2)}.
\tag{9.20}
```

The squared mismatch is therefore the contact-defect summand times a bounded
factor. The bounds $\|A_*u\|+1+s/2\ge1$, $(1+s)(1-as)\le2$, and
$(1-b)^2\ge1/4$ give the coefficient $8$:

```math
g_*(s)^2
\le8\,\frac{(1+s)(s-b)^2}{1-as},
\qquad
\sum_i\lambda_i g_*(s_i)^2\le8\chi.
\tag{9.21}
```

**Step 5: recover the center and collect the estimates.** Subtracting support
values expresses each projection of $c-c_*$ as the sum of the slack, the
model mismatch, and the shape error:

```math
(c-c_*)^Tu_i=-r_i-g_*(s_i)+\|A_*u_i\|-\|Au_i\|.
\tag{9.22}
```

Multiplication by $\lambda_i u_i$ and summation uses isotropy to recover
$c-c_*$ itself. The triangle and Bessel estimates in Section 6 give

```math
\|c-c_*\|\le4\epsilon+\sqrt{8\chi}+\|A-A_*\|_F
\le50\sqrt\epsilon.
\tag{9.23}
```

In this last estimate, $\sqrt{8\chi}\le16\sqrt\epsilon$, the shape term is
at most $30\sqrt\epsilon$, and $4\epsilon\le0.004\sqrt\epsilon$.
The coefficient $50$ is a single convenient upper bound for their sum.
Together with the completed proof of Lemma 6.1, these estimates justify
all deferred inputs in the proof of Theorem 6.2.

## 10. Discussion

The preceding sections establish the sharp contraction, equality, and stability
results. We now discuss extensions of the optimization and matrix viewpoints:
the unnormalized dual, the scope of the common rotation's optimality, an
alternative deficit identity, and the full family of coupled inequalities.
These results elaborate the earlier arguments; the core proofs are complete
without referring forward to this discussion.

### 10.1. The unnormalized dual and its scale

For the bounded full-dimensional polytope $\mathcal P$ of Section 2, retain
the primal formulation (2.3). The normalized certificate problem (2.8) was
chosen for a direct trace bound. The usual Lagrangian dual explains this
normalization and is useful when working with unnormalized multipliers.

This standard convex formulation is discussed in [BV2004, Section 8.4] and in the maximum-volume ellipsoid literature [ZG2003]. Self-duality of the Lorentz cone and the log-determinant conjugate give the dual

```math
\begin{aligned}
\text{minimize}_{\alpha,q}\quad&\sum_r\alpha_r\beta_r-n-\log\det M\\
\text{subject to}\quad&\sum_r\alpha_rg_r=0,\quad
\|q_r\|\le\alpha_r,\quad
M=\sum_r\operatorname{sym}(q_rg_r^T)\succ0.
\end{aligned}
\tag{10.1}
```

Indeed, with $s=\sum_r\alpha_r\beta_r$ the Lagrangian is

```math
\begin{aligned}
\mathcal L(A,c)&=\log\det A-\operatorname{tr}(AM)
-c^T\sum_r\alpha_rg_r+s,\\
\sup_{A\succ0,c}\mathcal L&=
\begin{cases}
s-n-\log\det M,&\sum_r\alpha_rg_r=0,\ M\succ0,\\
+\infty,&\text{otherwise}.
\end{cases}
\end{aligned}
\tag{10.2}
```

The finite supremum is attained at $A=M^{-1}$. This is the standard log-determinant conjugate calculation [BV2004, Chapters 3 and 5].

**Remove the redundant multiplier scale.** Balance and cone feasibility
are preserved by positive scaling. We can therefore optimize that one scalar
before considering the remaining dual variables. For a dual feasible point,
primal feasibility implies $s\ge\operatorname{tr}(AM)>0$.
Scaling all multipliers by $\rho>0$ gives
$\Psi(\rho)=\rho s-n-n\log\rho-\log\det M$. With $u=\rho s/n$,

```math
\Psi(\rho)-\Psi(n/s)=n(u-1-\log u)\ge0.
\tag{10.3}
```

Thus the optimal scale has $\sum_r\alpha_r\beta_r=n$, giving precisely
the normalized certificate problem (2.8). Its optimal value is the negative
of the primal optimal value, and both optima are attained, by Proposition 2.3.
A strictly feasible small ellipsoid also allows the use of Slater's theorem.
The construction in Section 2.3 additionally identifies optimal multipliers
from the contact geometry.

### 10.2. Optimality of the common rotation

<a id="prop-polar"></a>
**Proposition 10.1 (optimality among common contractions).** If $\|R\|_{\rm op}\le1$ and $N=\operatorname{sym}(RQ^T)\succ0$, then $\det N\le\det Q$. The rotation $R=U$ in (3.13) attains equality.

**Proof.** We compare the determinant with its positive symmetric part,
then use the contraction bound on $R$. Write $RQ^T=N+K$ with $K^T=-K$,
and normalize the skew part by $T=N^{-1/2}KN^{-1/2}$.
The following Gram determinant identity provides the first comparison:

```math
\det(I+T)^2=\det\bigl((I+T)^T(I+T)\bigr)
=\det(I+T^TT)\ge1
\tag{10.4}
```

gives $|\det(N+K)|\ge\det N$. Moreover,

```math
\|R\|_{\rm op}\le1
\quad\Longrightarrow\quad 0\preceq R^TR\preceq I
\quad\Longrightarrow\quad |\det R|^2=\det(R^TR)\le1.
\tag{10.5}
```

Consequently $\det N\le|\det(RQ^T)|=|\det R|\det Q\le\det Q$.
At $R=U$, (3.15) gives $N=M$ and equality. ∎

This restricted optimality does not rule out improvements from changing the multiplier directions individually. The proof uses only real positive-semidefinite matrices, avoiding a separate argument with complex eigenvalues of a skew-symmetric matrix.

### 10.3. An alternative deficit decomposition

This decomposition follows the same gap through singular-value estimates.
Its terms distinguish support slack, the triangle inequality for the nuclear
norm, and the scalar logarithmic inequality. A fourth term records the
difference between the resulting nuclear-norm bound and the trace used by
the polar certificate.
Let $\|\cdot\|_*$ denote the sum of singular values, and put

```math
\begin{aligned}
S&=\sum_i\alpha_i(1-c^Tu_i-\|Au_i\|)+t(-c^Tv-\|Av\|),\\
T_{\rm nuc}&=\sum_i\alpha_i\|Au_i\|+t\|Av\|-\|AQ\|_*,\\
H_{\rm nuc}&=\|AQ\|_*-n-\log\det(AQ),\\
\mathcal R_{\rm pol}&=\|AQ\|_*-\operatorname{tr}(AM).
\end{aligned}
\tag{10.6}
```

Primal feasibility gives $S\ge0$. For the other terms, use the standard rank-one and trace bounds for the nuclear norm [HJ1985]. If $\rho_j>0$ are the singular values of $AQ$, then

```math
\begin{aligned}
\|AQ\|_*
&\le\sum_i\alpha_i\|Au_i p_i^T\|_*+t\|Avv^T\|_*\\
&=\sum_i\alpha_i\|Au_i\|+t\|Av\|,\\
H_{\rm nuc}&=\sum_{j=1}^n(\rho_j-1-\log\rho_j)\ge0,\\
\operatorname{tr}(AM)&=\operatorname{tr}(AQU^T)
\le\|AQ\|_*\|U\|_{\rm op}=\|AQ\|_*.
\end{aligned}
\tag{10.7}
```

Here $\det(AQ)>0$ ensures $\sum_j\log\rho_j=\log\det(AQ)$.
All four terms are nonnegative. To relate them to the main deficit identity,
keep the polar correction explicitly: it is added to the cone gap and
subtracted from the matrix divergence, so it cancels in their sum.
Direct calculation gives

```math
\begin{aligned}
\mathcal C&=S+T_{\rm nuc}+\mathcal R_{\rm pol},\\
\mathcal D(A,M)&=H_{\rm nuc}-\mathcal R_{\rm pol},\\
\epsilon&=\log\det\widehat F+S+T_{\rm nuc}+H_{\rm nuc}.
\end{aligned}
\tag{10.8}
```

In general $\mathcal C\ne S+T_{\rm nuc}$, because multiplication by $A$ changes the polar factor. The correction vanishes when $A$ commutes with $M$. The cone-based identity (4.3) is more directly suited to equality and stability, because its two optimization terms separately measure complementarity and matrix matching.

### 10.4. General and complementary coupled inequalities

Lemma 8.6 extracted the particular coupling estimate used in the main proofs.
The same finite moment calculation gives an inequality for every symmetric
test matrix and every vector. We record that full statement and its companion
at the opposite endpoint of the trace range.

For these extensions introduce

```math
\begin{gathered}
h=d+b^2,\qquad\sigma_*:=\frac{2(1-b)}h,\qquad\tau=\sigma_*-\sigma,\\
e_*:=\frac{2b}h=\frac{\sigma_*}{m},\qquad
\bar\chi=\sum_i\nu_i(1-s_i)(s_i+b)^2.
\end{gathered}
\tag{10.9}
```

Here $\tau$ is the unused part of the allowed trace, $e_*=\sigma_*/m$,
and $\bar\chi$ is the complementary nonnegative contact sum.
The coefficient in Lemma 8.6 is $L=d\tau/2$.
The scalar relation (8.45) becomes
$\chi+(1-b)(2+b)^2\bar\chi/h^2=d(2+b)(1-b)/h$.

<a id="lem-cauchy"></a>
**Lemma 10.2 (coupled Cauchy inequality).** For every symmetric $Z\in\mathbb S^m$ and $q\in\mathbb R^m$,

```math
(\operatorname{tr}(ZE)+q^Tj)^2
\le\sigma\left[
\operatorname{tr}\bigl(Z^2(E+\tfrac12I_m)\bigr)
+2q^TZj+\frac d4\tau\|q\|^2\right].
\tag{10.10}
```

**Proof.** The aim is to represent the linear quantity on the left as one
weighted contact sum, so that one application of Cauchy–Schwarz controls both
parts. Choose $\gamma=\sqrt{d(1-b)}/h$; the moment identities then give

```math
\operatorname{tr}(ZE)+q^Tj
=-\frac1d\sum_i\nu_i(s_i-b)y_i^T\bigl(Zy_i+\gamma(s_i+b)q\bigr).
\tag{10.11}
```

The coefficient $\gamma$ is chosen so that the $q$ term is exactly $q^Tj$.
Apply $|y_i^Tw|\le\|y_i\|\|w\|$ to each summand and use
$\|y_i\|^2=(1-s_i)(1+s_i)$. In weighted Cauchy–Schwarz, the factors
$\nu_i(1+s_i)(s_i-b)^2$ sum to $\chi$, leaving the bound

```math
\frac{\chi}{d^2}\sum_i\nu_i(1-s_i)
\|Zy_i+\gamma(s_i+b)q\|^2.
\tag{10.12}
```

Terms at the poles have $y_i=0$, so no division by $1\pm s_i$ is needed.
Expanding the remaining squared norm produces a quadratic term in $Z$, a
mixed term in $Z,q$, and a quadratic term in $q$. The following three identities
evaluate them in that order:

```math
\begin{aligned}
\sum_i\nu_i(1-s_i)y_iy_i^T&=\frac{2d}{2+b}(E+\tfrac12I_m),\\
\gamma\sum_i\nu_i(1-s_i)(s_i+b)y_i&=\frac{2d}{2+b}j,\\
\gamma^2\bar\chi&=\frac{d^2}{2(2+b)}\tau.
\end{aligned}
\tag{10.13}
```

The first two follow from (8.44) and (8.47); the third uses the complementary
defect relation (8.45). Thus $\tau$ enters as the coefficient of the pure
$q$ term. Combining the three contributions gives

```math
\begin{aligned}
&\sum_i\nu_i(1-s_i)\|Zy_i+\gamma(s_i+b)q\|^2\\
&\qquad=\frac{2d}{2+b}\left[
\operatorname{tr}\bigl(Z^2(E+\tfrac12I_m)\bigr)
+2q^TZj+\frac d4\tau\|q\|^2\right].
\end{aligned}
\tag{10.14}
```

Substitution and $\sigma=2\chi/[d(2+b)]$ prove (10.10). ∎

**The complementary endpoint.** Replacing the transverse perturbation by
$e_*I_m-E$ replaces its trace $\sigma$ by $\tau$. The corresponding estimate is

<a id="lem-cauchy-minus"></a>
**Lemma 10.3 (complementary Cauchy inequality).** With the notation of Lemma 8.5, for every symmetric $Z$ and every $q$,

```math
\bigl(\operatorname{tr}(Z(e_*I_m-E))+q^Tj\bigr)^2
\le\tau\left[\operatorname{tr}\bigl(Z^2(tI_m-E)\bigr)
+2q^TZj+\frac d4\sigma\|q\|^2\right].
\tag{10.15}
```

**Proof.** Use the complementary defect $\bar\chi$ in the same weighted
Cauchy–Schwarz argument as Lemma 10.2. Choose
$c_-=(1-ab)/h$ and $\gamma_-=\sqrt d/[\sqrt{1-b}(2+b)]$ so that the
linear contact sum recovers both the shifted transverse block and the
coupling with the required coefficients. The moment identities give

```math
\operatorname{tr}(Z(e_*I_m-E))+q^Tj
=c_-\sum_i\nu_i(s_i+b)y_i^T\bigl(Zy_i-\gamma_-(s_i-b)q\bigr).
\tag{10.16}
```

Weighted Cauchy–Schwarz bounds the square of (10.16) by

```math
c_-^2\bar\chi\sum_i\nu_i(1+s_i)
\|Zy_i-\gamma_-(s_i-b)q\|^2.
\tag{10.17}
```

The complementary defect relation turns the first factor into a multiple of
$\tau$. The expanded squared norm contains the opposite transverse moment
$tI_m-E$. Using (8.47) and the moment identities gives

```math
\begin{aligned}
&c_-^2\bar\chi=\frac{(1-b)(2+b)}{2d}\tau,\\
&\sum_i\nu_i(1+s_i)\|Zy_i-\gamma_-(s_i-b)q\|^2\\
&\qquad=\frac{2d}{(1-b)(2+b)}\left[
\operatorname{tr}\bigl(Z^2(tI_m-E)\bigr)
+2q^TZj+\frac d4\sigma\|q\|^2\right].
\end{aligned}
\tag{10.18}
```

The prefactors cancel to give (10.15). Contacts with $s_i=\pm1$ have $y_i=0$, so the argument covers the poles without division by zero. ∎

Taking $Z=0$ in either (10.10) or (10.15) gives $\|j\|^2\le d\sigma\tau/4$.

### 10.5. Inverse-trace interpretation

<a id="lem-inverse-trace"></a>
**Lemma 10.4 (inverse-trace interpretation).** Suppose $0<\sigma<\sigma_*$. Set $\eta=d\tau/4$ and $x=d\sigma/4$. Then (10.10), for all $Z,q$, is equivalent to

```math
R_+=E+\frac12I_m-\frac{jj^T}{\eta}\succ0,
\qquad \operatorname{tr}(R_+^{-1})\le2m.
\tag{10.19}
```

Similarly, (10.15) is equivalent to

```math
R_-=tI_m-E-\frac{jj^T}{x}\succ0,
\qquad \operatorname{tr}(R_-^{-1})\le\frac{m}{t-e_*}.
\tag{10.20}
```

**Proof.** First absorb the mixed term by completing the square. Then identify
the best Cauchy–Schwarz coefficient and exhibit a test attaining it. This will
prove necessity as well as sufficiency of the inverse-trace bound.

**Step 1: separate the matrix and vector tests.** Complete the square in
(10.10) by setting $q=q'-Zj/\eta$. This shift removes the mixed quadratic term
and leaves $R_+$ as the effective matrix coefficient. The two forms become

```math
\begin{aligned}
\operatorname{tr}(ZE)+q^Tj
&=\operatorname{tr}\bigl(Z(R_+-\tfrac12I_m)\bigr)+q'^Tj,\\
\operatorname{tr}\bigl(Z^2(E+\tfrac12I_m)\bigr)+2q^TZj+\eta\|q\|^2
&=\operatorname{tr}(Z^2R_+)+\eta\|q'\|^2.
\end{aligned}
\tag{10.21}
```

Before using its inverse, establish strict positivity from the inequality
itself. If $w^TR_+w<0$, the choice $Z=ww^T$, $q'=0$ makes its right-hand side
negative. If $R_+w=0$ for $w\ne0$, the same choice gives zero on the right and
$(-\|w\|^2/2)^2>0$ on the left. Thus $R_+\succ0$.

**Step 2: identify the coefficient required for every test.**
Diagonalize $R_+$ and apply weighted Cauchy–Schwarz to the diagonal entries
of $Z$ and to $q'$; off-diagonal entries contribute only nonnegative terms to
$\operatorname{tr}(Z^2R_+)$. The resulting coefficient is

```math
\begin{aligned}
S_+
&=\operatorname{tr}\bigl((R_+-\tfrac12I_m)^2R_+^{-1}\bigr)
+\frac{\|j\|^2}{\eta}\\
&=\operatorname{tr}R_+-m+\frac14\operatorname{tr}(R_+^{-1})
+\frac{\|j\|^2}{\eta}\\
&=\sigma-\frac m2+\frac14\operatorname{tr}(R_+^{-1}).
\end{aligned}
\tag{10.22}
```

To show that no smaller coefficient suffices, use the test attaining equality
in these scalar Cauchy–Schwarz inequalities:

```math
Z_+=I_m-\frac12R_+^{-1},\qquad q'_+=j/\eta.
\tag{10.23}
```

At this test the linear form and the quadratic form both equal $S_+$.
The cancellation in (10.22) leaves only the inverse trace to be bounded.
Consequently, the inequality for all $Z,q$ is equivalent to $S_+\le\sigma$, or
$\operatorname{tr}(R_+^{-1})\le2m$. This proves both directions of (10.19), including the case $S_+=0$.

**Step 3: apply the same argument at the complementary endpoint.**
For (10.15), set $q=q'-Zj/x$ and put
$\beta=t-e_*=(1-b)^2(2+b)/(2h)>0$. The completed forms have the same shape with
$(R_+,\tfrac12,\eta)$ replaced by $(R_-,\beta,x)$. The rank-one tests again give $R_-\succ0$. Weighted Cauchy–Schwarz is attained at
$Z_-=I_m-\beta R_-^{-1}$, $q'_-=j/x$, with coefficient

```math
\begin{aligned}
S_-
&=\operatorname{tr}\bigl((R_--\beta I_m)^2R_-^{-1}\bigr)
+\frac{\|j\|^2}{x}\\
&=(-t+2e_*)m-\sigma+(t-e_*)^2\operatorname{tr}(R_-^{-1}).
\end{aligned}
\tag{10.24}
```

Since $\tau=me_*-\sigma$,

```math
S_-\le\tau
\iff (t-e_*)^2\operatorname{tr}(R_-^{-1})\le m(t-e_*)
\iff \operatorname{tr}(R_-^{-1})\le\frac{m}{t-e_*}.
\tag{10.25}
```

This is (10.20), with both implications proved. ∎

### 10.6. Further models and extensions

For a simplex with vertices $x_0,\ldots,x_n$ and centroid $\bar x$, the standard
affine-transport formula is $J(\Delta)=\bar x+H_\Delta^{1/2}B_2^n$, where
$H_\Delta=[n(n+1)]^{-1}\sum_i(x_i-\bar x)(x_i-\bar x)^T$.
It follows by transporting the regular-simplex inball. The main proof needs
only its contact configuration and the support calculation in Section 3.2.

For a full-dimensional offset-cut polytope, the same dual construction uses
the changed normalization below. For several cuts, the balance condition
contains all their normals:

```math
\sum_i\alpha_i+\eta\alpha_0=n\quad(v^Tx\le\eta),\qquad
\sum_i\alpha_iu_i+\sum_\ell\alpha_\ell v_\ell=0.
\tag{10.26}
```

These formulations identify how the certificate changes under additional constraints. Quantitative bounds for offset cuts and successive recentered cuts are natural directions for further research, alongside exact offset profiles and sharp bounds for prescribed simultaneous cuts.

For completeness, the Lorentz transformation underlying (3.7) is

```math
\begin{pmatrix}1&-av^T\\-av&vv^T+kP\end{pmatrix}\binom1u
=\binom{1-as}{(s-a)v+kPu},\qquad s=u^Tv.
\tag{10.27}
```

Dividing the second component by the positive first component gives the unit
direction $p$ used in the certificate. This is the same construction in every
dimension; the dimensional distinction lies in its determinant proof.

## 11. Conclusion

The sharp central-cut factor is $R_n$ in every positive dimension, and equality is attained. An explicit certificate links the original John contacts to an upper bound on the new ellipsoid volume. The exact deficit identity then separates contact geometry, cone complementarity, and shape matching, yielding the complete equality family and quantitative stability.

The certificate construction is uniform in dimension, while its determinant proof still treats dimensions two, three, and at least four separately. A unified proof and sharper stability constants remain natural questions. Further directions include bounds for offset cuts, quantitative contraction over successive cuts, and certified cuts through approximate centers. Exact offset profiles, sharp simultaneous-cut bounds, and quantitative correction costs for computed centers remain open; whole-body stability requires hypotheses compatible with the nonunique equality family.

The results also clarify the role of inscribed ellipsoids in localization: contraction controls the potential, rounding controls a coordinate normalization, and a feasible primal–dual gap certifies the quality of an ellipsoid computation. These statements keep geometric progress separate from the cost and precision of centering. The analytical proofs are accompanied by a completed Lean 4 formalization.

**Formal verification and reproducibility.** The formalization uses Lean `v4.35.0-rc2` and mathlib at commit `0a6c8e0355da0405d616f80b9f8232c4fab2cc5b` [deMouraUllrich2021; Mathlib2020]. It covers all 28 named results and their supporting mathematical statements, with explicit correspondences for all 198 numbered equations. Independent source builds and transitive axiom audits accept only `propext`, `Classical.choice`, and `Quot.sound`. The accompanying source distribution, `SharpContractionCutJohnEllipsoid`, provides pinned dependencies, statement maps, and reproducible verification scripts. The three cited background assertions concerning centroid cuts and algorithmic complexity in Section 1.1 are outside the agreed formalization scope.

## References
- **[John1948]** Fritz John. Extremum problems with inequalities as subsidiary conditions. In *Studies and Essays Presented to R. Courant on His 60th Birthday*, pp. 187–204. Interscience, New York, 1948.
- **[GG2007]** Osman Güler and Filiz Gürtuna. *The extremal volume ellipsoids of convex bodies, their symmetry properties, and their determination in some special cases*. arXiv:0709.0707, version 1, 2007. [arXiv](https://arxiv.org/abs/0709.0707v1).
- **[TKE1988]** S. P. Tarasov, L. G. Khachiyan, and I. I. Erlikh. The method of inscribed ellipsoids. *Doklady Akademii Nauk SSSR* **298**(5), 1081–1085, 1988. English translation: *Soviet Mathematics Doklady* **37**, 226–230.
- **[Khachiyan1990]** L. G. Khachiyan. An inequality for the volume of inscribed ellipsoids. *Discrete & Computational Geometry* **5**, 219–222, 1990. [DOI](https://doi.org/10.1007/BF02187786).
- **[Zhou2026]** Zhou Longfei, Haijun Zou, and Tianhao Liu. *A Spectral Proof of Khachiyan's Ellipsoid Conjecture*. arXiv:2609.28447, version 1, 2026. [arXiv](https://arxiv.org/abs/2609.28447v1).
- **[BV2004]** Stephen Boyd and Lieven Vandenberghe. *Convex Optimization*. Cambridge University Press, 2004. Sections 8.4–8.5 discuss ellipsoids and centers; Chapters 9 and 11 and Appendix C discuss numerical methods and arithmetic cost.
- **[NN1994]** Y. Nesterov and A. Nemirovskii. *Interior-Point Polynomial Algorithms in Convex Programming*. SIAM, Philadelphia, 1994.
- **[HJ1985]** Roger A. Horn and Charles R. Johnson. *Matrix Analysis*. Cambridge University Press, 1985.
- **[GLS1988]** Martin Grötschel, László Lovász, and Alexander Schrijver. *Geometric Algorithms and Combinatorial Optimization*. Springer, Berlin, 1988.
- **[Grunbaum1960]** Branko Grünbaum. Partitions of mass-distributions and of convex bodies by hyperplanes. *Pacific Journal of Mathematics* **10**(4), 1257–1261, 1960. [DOI](https://doi.org/10.2140/pjm.1960.10.1257).
- **[AV1995]** D. S. Atkinson and P. M. Vaidya. A cutting plane algorithm for convex programming that uses analytic centers. *Mathematical Programming* **69**, 1–43, 1995.
- **[Vaidya1996]** P. M. Vaidya. A new algorithm for minimizing convex functions over convex sets. *Mathematical Programming* **73**, 291–341, 1996.
- **[Anstreicher1997]** Kurt M. Anstreicher. On Vaidya's volumetric cutting plane method for convex programming. *Mathematics of Operations Research* **22**, 63–89, 1997.
- **[KT1993]** Leonid G. Khachiyan and Michael J. Todd. On the complexity of approximating the maximal inscribed ellipsoid for a polytope. *Mathematical Programming* **61**, 137–159, 1993. [DOI](https://doi.org/10.1007/BF01582144).
- **[Anstreicher2002]** Kurt M. Anstreicher. Improved complexity for maximum volume inscribed ellipsoids. *SIAM Journal on Optimization* **13**(2), 309–320, 2002. The locally available author manuscript is dated 13 June 2001.
- **[ZG2003]** Yin Zhang and Liyan Gao. On numerical solution of the maximum volume ellipsoid problem. *SIAM Journal on Optimization* **14**(1), 53–76, 2003. [DOI](https://doi.org/10.1137/S1052623401397230).
- **[Todd2023]** Michael J. Todd. *The ellipsoid method redux*. arXiv:2301.07632, version 2, 2023. [arXiv](https://arxiv.org/abs/2301.07632v2).
- **[deMouraUllrich2021]** Leonardo de Moura and Sebastian Ullrich. The Lean 4 theorem prover and programming language. In *Automated Deduction — CADE 28*, Lecture Notes in Computer Science **12699**, pp. 625–635. Springer, 2021. [DOI](https://doi.org/10.1007/978-3-030-79876-5_37).
- **[Mathlib2020]** The mathlib Community. The Lean mathematical library. In *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs*, CPP 2020. ACM, 2020. [DOI](https://doi.org/10.1145/3372885.3373824).
