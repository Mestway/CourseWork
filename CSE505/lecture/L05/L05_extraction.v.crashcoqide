(** * IMP Extraction *)

Require Import ZArith.
Require Import String.

Open Scope string_scope.
Open Scope Z_scope.

Require Import L05_syntax.
Require Import L05_semantics.

Definition fib_x_y : stmt :=
  "y"  <- 0;;
  "y0" <- 1;;
  "y1" <- 0;;
  "i"  <- 0;;
  while ("i" [<] "x") {{
    "y"  <- "y0" [+] "y1";;
    "y0" <- "y1";;
    "y1" <- "y";;
    "i"  <- "i" [+] 1
  }}.

Definition gcd_xy_i : stmt :=
  "i" <- "x";;
  while (0 [<] "x" [%] "i" [||]
         0 [<] "y" [%] "i") {{
    "i" <- "i" [-] 1
  }}.

Extraction interp_expr.
Extraction interp_step.
Extraction run.

Extraction fib_x_y.
Extraction gcd_xy_i.

(** we can also make versions of our programs
    that set up an useful initial heaps *)

Definition fib_prog (x: Z) : stmt :=
  "x" <- x;;
  fib_x_y.

Definition gcd_prog (x y: Z) : stmt :=
  "x" <- x;;
  "y" <- y;;
  gcd_xy_i.

(** use analogous OCaml types *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlString.

(** we can even put these in a file and run them! *)
Cd "~/505-au15/www/L05/".
Extraction "Imp.ml" run empty fib_prog gcd_prog.
