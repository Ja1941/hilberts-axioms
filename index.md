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
    First, we need to prove that the three points are not on line $CE$. This is not as easy as it looks on the graph, which involves a series of collinearity arguments. Then as       line $CE$ intersects $AD$ at $C$, Pasch's says it either intersects $AB$ or $BD$. The first case is exactly what we want, and the second case leads to a contradiction: if they     intersect at $P$, which is also the intersection of line $CE$ and line $BD$ that is supposed to be $E$. By uniqueness, $P = E$ but $B*P*D$ and $B*D*E$, contradiction by our       axioms.
    </p>
    <img src="draft/between.jpg" alt="Existence of a point between any two distinct ones" width="250" height="150">
    
    <h2>lemma same_side_line_trans</h2>
    
    <p>
    This lemma proves the transitivity of the relation two points being on the same side to a line. The proof is divided into two parts, when the three points are collinear and       the converse. The noncollinear case is proven in same_side_line_trans_noncol and we will need it for the collinear case. This case is easily done by Pasch's. $A$ $B$ $C$ are noncollinear and not on $l$. Also, we have $l$ not intersecting $AB$ and $BC$ and want to prove it doesn't intersect $AC$. If it does, Pasch says $l$ must intersect with either $AB$ or $BC$, which is contradictive.
    </p>
    <img src="draft/noncol.PNG" alt="noncollinear case" width="250" height="150">
  
    <p>
    Proof when they are collinear involves contruction of three noncollinear points to apply the noncollinear case. Assume $A$ $B$ $C$ all lie on $m$. $m$ intersects with $l$ in at most one point, so there must exist $D$ on $l$ but not on $m$. Then extend $D$ $A$ to get $E$. Now $A$ and $E$ are on the same side to $l$ since line $AE$ already intersects with $l$ at $D$, which is not on segment $AE$. Also note that $A$ $B$ $E$ must be noncollinear and $A$ $B$ are on the same side to $l$. By the noncollinear case, $B$ $E$ are on the same side. Also $B$ $C$ $E$ are noncollinear and $B$ $C$ are on the same side. Again by the noncollinear case, $C$ $E$ are on the same side. Lastly, $A$ $C$ $E$ are noncollinear and $A$ $E$ are on the same side as proven before, $A$ $C$ are on the same side.
    </p>
  <img src="draft/col.PNG" alt="collinear case" width="250" height="150">
  
  <h2>theorem crossbar</h2>
  
  <p>
    This theorem states that the ray $AD$ inside $∠BAC$ must meet $BC$. We will prove it based on Pasch's and a series of sidedness reasoning.
    <img src="draft/crossbar1.PNG" alt="Crossbar theorem" width="250" height="150">
  </p>
  
  <p>
    First, we extend $C$ $A$ to $E$. Apply Pasch's on line $AD$ and points $E$ $B$ $C$ and we know $AD$ intersect with either $BE$ or $BC$. The proof is divided into the following steps.
 <ul>
  <li>$BE$ doesn't intersect with ray $AD$.</li>
  <li>$BE$ doesn't intersect with the opposite ray of $AD$, so $BE$ doesn't intersect with line $AD$ so line $AD$ will meet $BC$.</li>
  <li>$BC$ doesn't meet the opposite ray of $AD$, so it must meet ray $AD$.</li>
</ul>
  </p>
  <img src="draft/crossbar1.PNG" alt="Crossbar theorem proof" width="250" height="150">
</body>
