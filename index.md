<head>
  <meta charset="utf-8">
  <meta http-equiv="x-ua-compatible" content="ie=edge">
  <meta name="viewport" content="width=device-width">
  <title>MathJax v3 with TeX input and HTML output</title>
  <script src="https://polyfill.io/v3/polyfill.min.js?features=es6"></script>
  <script>
  MathJax = {
    tex: {inlineMath: [['$', '$'], ['\\(', '\\)']]}
  };
  </script>
  <script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js"></script>
</head>
<body>
    
    <h2>Notations</h2>
    <p> $AB$ : segment $A$ $B$ </p>
    <p> $A*B*C$ : $B$ is between $A$ and $C$ </p>
  
    <h2>Pasch's axiom B4</h2>
    <p>
    This axiom says that if a line enters a triangle in one side, it must exit in one of the two other sides, but not both. As in the figure, $A$, $B$ and $C$ are not on $l$           and $l$ intersects with segment $AB$, so it should intersect with either $AC$ or $BC$.
    </p>
    <img src="draft/pasch.PNG" alt="Pasch's" width="250" height="150">

    <h2>lemma two_pt_between</h2>

    <p>
    This lemma asserts the existence of a point between two distinct points, using Pasch's. Given two distinct points $A$ and $B$, we find another point $C$ such that they are         noncollinear. Then we extend $A$ and $C$ to $D$, $B$ and $D$ to $E$ and use Pasch's on points $A$ $B$ $D$ and line $CE$.
    </p>
    <p>
    First we need to prove that the three points are not on $(C-ₗE)$. This is not as easy as it looks on the graph, which involves a series of collinearity arguments. Then as line     $CE$ intersects $AD$ at $C$, Pasch's says it either intersects $AB$ or $BD$. The first case is exactly what we want, and the second case leads to a contradiction: if they         intersect at $x$, which is also the intersection of line $CE$ and \underline{line} $BD$ that is supposed to be $E$. By uniqueness, $x = E$ but $B*x*D$ and $B*D*E$, which is       contradiction by our axioms.
    </p>
    <img src="draft/between.JPG" alt="Existence of a point between any two" width="250" height="150">

    <h2>The Cauchy-Schwarz Inequality</h2>

    <p>\[
    \left( \sum_{k=1}^n a_k b_k \right)^{\!\!2} \leq
     \left( \sum_{k=1}^n a_k^2 \right) \left( \sum_{k=1}^n b_k^2 \right)
    \]</p>

    <h2>A Cross Product Formula</h2>

    <p>\[
      \mathbf{V}_1 \times \mathbf{V}_2 =
       \begin{vmatrix}
        \mathbf{i} &amp; \mathbf{j} &amp; \mathbf{k} \\
        \frac{\partial X}{\partial u} &amp; \frac{\partial Y}{\partial u} &amp; 0 \\
        \frac{\partial X}{\partial v} &amp; \frac{\partial Y}{\partial v} &amp; 0 \\
       \end{vmatrix}
    \]</p>

    <h2>The probability of getting \(k\) heads when flipping \(n\) coins is:</h2>

    <p>\[P(E) = {n \choose k} p^k (1-p)^{ n-k} \]</p>

    <h2>An Identity of Ramanujan</h2>

    <p>\[
       \frac{1}{(\sqrt{\phi \sqrt{5}}-\phi) e^{\frac25 \pi}} =
         1+\frac{e^{-2\pi}} {1+\frac{e^{-4\pi}} {1+\frac{e^{-6\pi}}
          {1+\frac{e^{-8\pi}} {1+\ldots} } } }
    \]</p>

    <h2>A Rogers-Ramanujan Identity</h2>

    <p>\[
      1 +  \frac{q^2}{(1-q)}+\frac{q^6}{(1-q)(1-q^2)}+\cdots =
        \prod_{j=0}^{\infty}\frac{1}{(1-q^{5j+2})(1-q^{5j+3})},
         \quad\quad \text{for $|q| &lt; 1$}.
    \]</p>

    <h2>Maxwell's Equations</h2>

    <p>
    \begin{align}
      \nabla \times \vec{\mathbf{B}} -\, \frac1c\, \frac{\partial\vec{\mathbf{E}}}{\partial t} &amp; = \frac{4\pi}{c}\vec{\mathbf{j}} \\
      \nabla \cdot \vec{\mathbf{E}} &amp; = 4 \pi \rho \\
      \nabla \times \vec{\mathbf{E}}\, +\, \frac1c\, \frac{\partial\vec{\mathbf{B}}}{\partial t} &amp; = \vec{\mathbf{0}} \\
      \nabla \cdot \vec{\mathbf{B}} &amp; = 0
    \end{align}
    </p>

    <h2>In-line Mathematics</h2>

    <p>Finally, while display equations look good for a page of samples, the
    ability to mix math and text in a paragraph is also important.  This
    expression $\sqrt{3x-1}+(1+x)^2$ is an example of an inline equation.  As
    you see, MathJax equations can be used this way as well, without unduly
    disturbing the spacing between lines.</p>
    <img src="draft/pasch.PNG" alt="Pasch's" width="500" height="333">
  
</body>
