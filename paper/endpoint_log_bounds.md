# Verification of the endpoint constant comparison

The report states the endpoint constant comparison directly. This supporting record
retains its exact rational certificate. Display numbers below belong to the
layout before this material was removed from the main text.

The exact value is $\mathcal R(1/4)=(2106\log13-468\log2-4160)/925$.

Use $\log13=4\log2-\log(16/13)$.
An upper bound for $\log2$ and a lower bound for $\log(16/13)$ will therefore
give an upper bound for $\mathcal R(1/4)$.
Both follow from
$\log((1+x)/(1-x))=2\int_0^x(1-u^2)^{-1}\,du$ for $0<x<1$.

For $x=1/3$, the finite identity
$(1-u^2)^{-1}=1+u^2+u^4+u^6/(1-u^2)$ and
$(1-u^2)^{-1}\le9/8$ on this interval give

```math
\log2\le
2\left(\frac13+\frac1{81}+\frac1{1215}\right)+\frac1{6804}
=\frac{23581}{34020}.
\tag{8.34}
```

For $x=3/29$, retaining $1+u^2$ and discarding the nonnegative remainder gives

```math
\log(16/13)\ge
2\left(\frac3{29}+\frac{(3/29)^3}{3}\right)
=\frac{5064}{24389}.
\tag{8.35}
```

Substitution now leaves an exact rational comparison:

```math
\begin{aligned}
\mathcal R(1/4)
&=\frac{7956\log2-2106\log(16/13)-4160}{925}\\
&\le\frac{21144601309}{21319034625}
<\frac{9919}{10000}<\frac{124}{125}.
\end{aligned}
\tag{8.36}
```
