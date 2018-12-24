(*
  5:59 7:55 coding
  3:57 4:45 coding
  zojirushi $20 

  This module defines an abstract theory of
  Incidence geoemetry.
*)

Require Import base.
Require Import List.
Require Import Bool.
Require Import Classical.
Require Import Description.

Module Incidence.

(* Represents an abstract Incidence geometry. *)
Structure Incidence : Type := incidence {
  (* Represents the set of points. *)
  point : Set;

  (* Asserts that equality between points is decideable. *)
  point_eq_dec : forall p q : point, { p = q } + { p <> q };

  (*
    Accepts three points and asserts that
    they are distinct.
  *)
  distinct
    :  point -> point -> point -> Prop
    := fun p q r => p <> q /\ p <> r /\ q <> r;

  (* Represents the set of lines. *)
  line : Set;

  (* Asserts that equality between lines is decideable. *)
  line_eq_dec : forall l m : line, { l = m } + { l <> m };

  (*
    Accepts a line and a point and returns true
    iff the point lies on the line.
  *)
  on : line -> point -> bool;

  (*
    Asserts that three points A, B  and c are
    collinear if there exists one line l such
    that all three points A, B, and C all lie
    on l.
    Accepts three points and returns true iff
  *)
  collinear
    :  point -> point -> point -> Prop
    := fun p q r : point
         => exists l : line, on l p = true /\ on l q = true /\ on l r = true; 

  (*
    Accepts three points and returns true iff
    they are not collinear.
  *)
  noncollinear
    :  point -> point -> point -> Prop
    := fun p q r => ~ collinear p q r;

  (*
    Two lines l and m are said to be parallel
    if there is no point P such that P lies on
    both  l and m.
  *)
  parallel
    :  line -> line -> Prop
    := fun l m => ~ exists p : point, on l p = true /\ on m p = true;

  (*
    Accepts two lines and returns true iff they
    are not parallel.
  *)
  nonparallel 
    :  line -> line -> Prop
    := fun l m => ~ parallel l m;

  (*
    Asserts that for every pair of distinct
    points P and Q there exists exactly one line
    l such that both P and Q lie on l.
  *)
  points_line_axiom : forall p q : point, p <> q -> exists! l : line, on l p = true /\ on l q = true;

  (*
    Asserts that for every line l there exists
    at least two distinct points P and Q such
    that both P and Q lie on l.
  *)
  line_points_axiom : forall l : line, exists p : point, exists q : point, p <> q -> on l p = true /\ on l q = true;

  (*
    Asserts that there exists three points that
    do not lie on any one line.

    Note: we must add the distinct condition or
    we could satisfy these axioms with a single
    point geometry.
  *)
  collinearity_axiom : exists p : point, exists q : point, exists r : point, distinct p q r /\ noncollinear p q r
}.

Arguments point_eq_dec {i} p q.
Arguments distinct {i} p q r.
Arguments line_eq_dec {i} l m.
Arguments on {i} l p.
Arguments collinear {i} p q r.
Arguments noncollinear {i} p q r.
Arguments parallel {i} l m.
Arguments nonparallel {i} l m.
Arguments points_line_axiom {i} p q H.
Arguments line_points_axiom {i} l.

Section Theorems.

(* Represents an arbitrary incidence geometry. *)
Variable g : Incidence.

(* Abbreviations. *)
Let point := point g.
Let line := line g.

(* Proves that at least two distinct lines exist. *)
Definition lines_ex
  :  exists l : line, exists m : line, l <> m
  := ex_ind (fun p : point =>
     ex_ind (fun q : point => 
     ex_ind (
       fun (r : point) (H : distinct p q r /\ noncollinear p q r)
         => ex_ind
              (fun (l : line) (H0 : unique (fun l => on l p = true /\ on l q = true) l)
                => ex_ind
                     (fun (m : line) (H1 : unique (fun m => on m q = true /\ on m r = true) m)
                       => ex_intro
                            (fun x => exists y : line, x = y -> False)
                            l
                            (ex_intro
                              (fun y => l = y -> False)
                              m
                              (fun H2 : l = m
                                => proj2 H
                                     (ex_intro
                                       (fun n => on n p = true /\ on n q = true /\ on n r = true)
                                       l
                                       (conj
                                         (proj1 (proj1 H0))
                                         (conj
                                           (proj2 (proj1 H0))
                                           (proj2 (proj1 H1)
                                            || on a r = true @a by H2)))))))
                     (points_line_axiom q r
                       (proj2 (proj2 (proj1 H)))))
               (points_line_axiom p q
                 (proj1 (proj1 H))))))
     (collinearity_axiom g).
 
Set Opaque lines_ex.

(*
  Proves that every pair of nonparallel lines
  have a point that lies on both lines.

  Note: this theorem uses the double negation
  rule from classical logic.
*)
Definition nonparallel_thm 
  :  forall l m : line, nonparallel l m -> exists p : point, on l p = true /\ on m p = true
  := fun l m (H : ~ ~ exists p, on l p = true /\ on m p = true)
       => NNPP (exists p, on l p = true /\ on m p = true) H.

Set Opaque nonparallel_thm.

(*
  If l and m are distinct nonparallel lines then
  there exists a unique point P such that P lies
  on both l and m.
*)
Definition unique_point_intersect_thm
  :  forall l m : line, l <> m -> nonparallel l m -> exists! p : point, on l p = true /\ on m p = true
  := fun l m H H0
       => let (p, H1) := nonparallel_thm l m H0 in
          ex_intro 
            (unique (fun p => on l p = true /\ on m p = true))
            p
            (conj H1
              (fun (q : point) (H2 : on l q = true /\ on m q = true)
                => sumbool_ind
                     (fun _ => p = q)
                     (fun H3 : p = q => H3)
                     (fun H3 : p <> q
                       => ex_ind
                            (fun n (H4 : unique (fun n => on n p = true /\ on n q = true) n)
                              => let H5
                                   :  on l p = true /\ on l q = true
                                   := conj (proj1 H1) (proj1 H2) in
                                 let H6
                                   :  on m p = true /\ on m q = true
                                   := conj (proj2 H1) (proj2 H2) in
                                 (False_ind
                                   (p = q)
                                   (H
                                     ((proj2 H4) m H6
                                      || a = m @a by <- (proj2 H4) l H5))))
                            (points_line_axiom p q H3))
                     (point_eq_dec p q))).

Set Opaque unique_point_intersect_thm.

(*
  Accepts two arguments, a point, p, and a list
  of points, qs, and asserts that none of the
  points in qs equal p.
*)
Definition point_list_different
  :  point -> list point -> Prop
  := fun p qs => Forall (fun q => q <> p) qs.

(*
  Accepts two arguments, a point, p, and a list
  of points, qs, and asserts that none of the
  points in qs equal p.
*)
Definition point_list_differentb
  :  point -> list point -> bool
  := fun p
       => list_rec
            (fun _ => bool)
            true
            (fun q qs (F : bool)
              => sumbool_rec
                   (fun _ => bool)
                   (fun H : q = p => false)
                   (fun H : q <> p => F)
                   (point_eq_dec q p)). 

(*
  Given a point, p, a list of points, qs, and
  a proof that p is not in qs, proves that p is
  not in the tail of qs either.
*)
Definition point_list_differentb_tail
  :  forall (p q : point) (qs : list point), point_list_differentb p (cons q qs) = true -> point_list_differentb p qs = true
  := fun p q qs
       => let t qs := point_list_differentb p qs = true in
          sumbool_ind
            (fun _ => t (cons q qs) -> t qs)
            (fun (H : point_list_differentb p qs = true) _
              => H)
            (fun (H : point_list_differentb p qs = false)
              => sumbool_ind
                   (fun H0 => sumbool_rec _ _ _ H0 = true -> t qs)
                   (fun (H0 : q = p) (H1 : false = true)
                     => False_ind
                          (t qs)
                          (diff_false_true H1))
                   (fun (H0 : q <> p) (H1 : t qs)
                     => (*
                          Note: technically we can just return H1, but that
                          would obscure the fact that this branch represents
                          a logical contradiction.
                        *)
                        False_ind
                          (t qs)
                          (diff_true_false
                            (H || a = false @a by <- H1)))
                   (point_eq_dec q p))
            (bool_dec0 (point_list_differentb p qs)).

Set Opaque point_list_differentb_tail.

(*
  Given a point, p, a list of points qs, and a
  proof that p is not in qs, proves that p does
  not equal the head of qs.
*)
Definition point_list_differentb_head
  :  forall (p q : point) (qs : list point), point_list_differentb p (cons q qs) = true -> q <> p
  := fun p q qs 
       => sumbool_ind
            (fun H 
              (*
                partial evaluation of point_list_differentb p (cons
                q qs) using: 

                Eval lazy beta delta [point_list_differentb
                list_rect list_rec] iota in (point_list_differentb
                p (cons q qs)).
              *)
              => (sumbool_rec _ _
                   (fun _ => (fix F (l : list point) : bool := _) qs)
                   H) = true -> q <> p)
            (fun (H : q = p) (H0 : false = true)
              => False_ind
                   (q <> p)
                   (diff_false_true H0))
            (fun (H : q <> p) _ => H)
            (point_eq_dec q p).

Set Opaque point_list_differentb_head.

(*
  Accepts a point, p, and a list of points,
  qs, where p is different from the head of
  qs and from every element in the tail of qs,
  and proves that p is not in qs.
*)
Definition point_list_differentb_ind
  :  forall (p q : point) (qs : list point), q <> p -> point_list_differentb p qs = true -> point_list_differentb p (cons q qs) = true
  := fun p q qs H H0
       => sumbool_ind
            (fun H1
              => sumbool_rec
                   (fun _ => bool)
                   (fun H : q = p => false)
                   (fun H : q <> p
                     => (fix F (rs : list point) : bool := _) qs)
                   H1 = true)
            (fun H1 : q = p
              => False_ind _ (H H1))
            (fun _
              => H0)
            (point_eq_dec q p).

Set Opaque point_list_differentb_ind.

(*
  Proves that point_list_differentb and
  point_list_different are equivalent.
*)
Definition point_list_differentb_thm
  :  forall (p : point) (qs : list point), point_list_differentb p qs = true <-> point_list_different p qs
  := fun p
       => list_ind
            (fun qs => point_list_differentb p qs = true <-> point_list_different p qs)
            (conj
              (fun _ => Forall_nil (fun q => q <> p))
              (fun _ => eq_refl true))
            (fun q qs (F : point_list_differentb p qs = true <-> point_list_different p qs)
              => conj
                   (fun H : point_list_differentb p (cons q qs) = true
                     => Forall_cons q
                          (point_list_differentb_head p q qs H)
                          ((proj1 F) (point_list_differentb_tail p q qs H) : Forall (fun q => q <> p) qs))
                   (fun H : point_list_different p (cons q qs)
                     => Forall_ind
                          (fun rs => point_list_differentb p rs = true)
                          (eq_refl true)
                          (fun r rs (H : r <> p) (H0 : point_list_different p rs)  (H1 : point_list_differentb p rs = true)  
                            => point_list_differentb_ind p r rs H
                                 (H1))
                          H)).

Set Opaque point_list_differentb_thm.

(*
  Given a point, p, a list of points qs, and a
  proof that p is not in qs, proves that p does
  not equal the head of qs.
*)
Definition point_list_different_head
  :  forall (p q : point) (qs : list point), point_list_different p (cons q qs) -> q <> p
  := fun p q qs H
       => point_list_differentb_head p q qs
            (proj2 (point_list_differentb_thm p (q :: qs)) H).

Set Opaque point_list_different_head.

(*
  Given a point, p, a list of points, qs, and
  a proof that p is not in qs, proves that p is
  not in the tail of qs either.
*)
Definition point_list_different_tail
  :  forall (p q : point) (qs : list point), point_list_different p (q :: qs) -> point_list_different p qs
  := fun p q qs H
       => proj1 (point_list_differentb_thm p qs)
            (point_list_differentb_tail p q qs
              (proj2 (point_list_differentb_thm p (q :: qs)) H)).

Set Opaque point_list_different_tail.

(*
  Accepts a point, p, and a list of points,
  qs, where p is different from the head of
  qs and from every element in the tail of qs,
  and proves that p is not in qs.
*)
Definition point_list_different_ind
  :  forall (p q : point) (qs : list point), q <> p -> point_list_different p qs -> point_list_different p (cons q qs)
  := fun p q qs H H0
       => (proj1 (point_list_differentb_thm p (q :: qs)))
            (point_list_differentb_ind p q qs H
              ((proj2 (point_list_differentb_thm p qs)) H0)).

Set Opaque point_list_different_ind.

(*
  Accepts a list of points and asserts that the
  list does not contain any duplicates.

  Note: this predicate is very similar to the
  NoDup predicate introduced by the standard
  List module.
*)
Inductive point_list_distinct : list point ->  Prop
  := point_list_distinct_nil  : point_list_distinct nil
  |  point_list_distinct_cons
    : forall (p : point) (qs : list point),
      point_list_different p qs ->
      point_list_distinct qs ->
      point_list_distinct (cons p qs).

(*
  Accepts a list of points and returns true iff
  the list does not contain any duplicates.
*)
Definition point_list_distinctb
  :  list point -> bool
  := list_rec
       (fun _ => bool)
       true
       (fun p qs F
         => point_list_differentb p qs && F).

(*
  Proves that point_list_distinctb and
  point_list_distinct are equivalent.
*)
Definition point_list_distinct_thm
  :  forall ps : list point, point_list_distinctb ps = true <-> point_list_distinct ps
  := list_ind
       (fun ps => point_list_distinctb ps = true <-> point_list_distinct ps)
       (conj
         (fun _ => point_list_distinct_nil)
         (fun _ => eq_refl true))
       (fun p ps (F : point_list_distinctb ps = true <-> point_list_distinct ps)
         => conj
              (fun H : point_list_distinctb (cons p ps) = true
                => let H0
                     :  point_list_differentb p ps = true /\ point_list_distinctb ps = true
                     := andb_prop
                          (point_list_differentb p ps)
                          (point_list_distinctb ps)
                          H in
                   point_list_distinct_cons p ps
                     ((proj1 (point_list_differentb_thm p ps)) (proj1 H0))
                     ((proj1 F) (proj2 H0)))
              (fun H : point_list_distinct (cons p ps)
                => point_list_distinct_ind
                     (fun rs => point_list_distinctb rs = true)
                     (eq_refl true)
                     (fun r rs (H0 : point_list_different r rs) (H1 : point_list_distinct rs) (H2 : point_list_distinctb rs = true)
                       => let H3
                            :  point_list_differentb r rs = true
                            := (proj2 (point_list_differentb_thm r rs)) H0 in
                          andb_true_intro (conj H3 H2))
                     (cons p ps)
                     H)).

Set Opaque point_list_distinct_thm.
 
(*
  Accepts two points and returns true iff they
  are equal.
*)
Definition point_eqb
  :  point -> point -> bool
  := fun p q
       => if point_eq_dec p q
            then true
            else false.

(*
  Accepts two points and returns true iff they
  are not equal.
*)
Definition point_neqb
  :  point -> point -> bool
  := fun p q
       => negb (point_eqb p q).

(*
  Proves that point_neqb is sound - i.e. that
  it returns true iff two points are different.
*)
Definition point_neqb_thm
  :  forall p q : point, point_neqb p q = true -> p <> q
  := fun p q
       => sumbool_ind
            (fun H => negb (if H then true else false) = true -> p <> q)
            (fun _ (H : false = true)
              => False_ind
                   (p <> q)
                   (diff_false_true H))
            (fun (H : p <> q) (_ : true = true)
              => H)
            (point_eq_dec p q).

Set Opaque point_negb_thm.
 
(* 
  Accepts a point, p, and a list of points,
  qs, and proves that, if every point in qs is
  different from p then `point_list_different p qs`.
*)
Definition point_list_neq_different
  :  forall (p : point) (qs : list point), (forall q : point, In q qs -> q <> p) -> point_list_different p qs
  := fun p qs H
       => proj2 (Forall_forall (fun q => q <> p) qs) H.

Set Opaque point_list_neq_different.

(*
  Accepts a point, p, and a list of points, qs,
  and proves that, if every point, q, in qs is
  not equal to p according to points_neqb then
  `point_list_different p qs`.
*)
Definition point_list_neqb_different
  :  forall (p : point) (qs : list point), (forall q : point, In q qs -> point_neqb q p = true) -> point_list_different p qs
  := fun p qs H
       => point_list_neq_different p qs
            (fun q H0 => point_neqb_thm q p (H q H0)).

Set Opaque point_list_neqb_different.

(*
  Accepts a point, p, and a list, ps, and removes
  all instances of p from ps.
*)
Definition point_list_delete
  :  forall (p : point) (ps : list point), {qs : list point | point_list_different p qs}
  := fun p ps
       => let qs := filter (fun q => point_neqb q p) ps in
          let H
            :  point_list_different p qs
            := point_list_neqb_different p qs
                 (fun q H
                   => proj2 (proj1 (filter_In (fun q => point_neqb q p) q ps) H)) in
          exist
            (point_list_different p)
            qs
            H.

(*
  Accepts a point, p, and a list of distinct
  points, ps, and returns a list of distinct
  points that are different than p.
*)
Definition point_list_deleteb
  :  forall (p : point) (ps : list point), {qs : list point | point_list_differentb p qs = true}
  := fun p ps
       => sig_rec
            (fun _ => {qs : list point | point_list_differentb p qs = true})
            (fun qs H
              => exist
                   (fun rs => point_list_differentb p rs = true)
                   qs
                   (proj2 (point_list_differentb_thm p qs) H))
            (point_list_delete p ps).

(*
  Accepts a list of distinct points and proves
  that the head of the list is different than
  all the remaining points and all the remaining
  points are distinct.
*)
Definition point_list_distinctb_inv
  :  forall (p : point) (ps : list point), point_list_distinctb (p :: ps) = true -> point_list_differentb p ps = true /\ point_list_distinctb ps = true
  := fun p ps (H : point_list_differentb p ps && point_list_distinctb ps = true)
       => andb_prop
            (point_list_differentb p ps) 
            (point_list_distinctb ps)
            H.

(*
  Accepts a list of distinct points and proves
  that the head of the list is different than
  all the remaining points and all the remaining
  points are distinct.
*)
Definition point_list_distinct_inv
  :  forall (p : point) (ps : list point), point_list_distinct (p :: ps) -> point_list_different p ps /\ point_list_distinct ps
  := fun p ps H
       => let H0
            :  point_list_distinctb (p :: ps) = true
            := proj2 (point_list_distinct_thm (p :: ps)) H in
          let H1
            :  point_list_differentb p ps = true /\ point_list_distinctb ps = true
            := point_list_distinctb_inv p ps H0 in
          conj
            (proj1 (point_list_differentb_thm p ps) (proj1 H1))
            (proj1 (point_list_distinct_thm ps) (proj2 H1)). 

(*
  Accepts a list of points and proves that the
  head of the list is different than all of the
  remaining points.
*)
Definition point_list_distinct_different
  :  forall (p : point) (ps : list point), point_list_distinct (p :: ps) -> point_list_different p ps
  := fun p ps H
       => proj1 (point_list_distinct_inv p ps H).

(*
  Accepts a list of distinct points and proves
  that the tail of the list is a list of distinct
  points.
*)
Definition point_list_distinct_tail
  :  forall (p : point) (ps : list point), point_list_distinct (p :: ps) -> point_list_distinct ps
  := fun p ps H
       => proj2 (point_list_distinct_inv p ps H).

(*
  Accepts two lists, xs and ys, and asserts that
  xs is a subset of ys.
*)
Definition set_list_subset
  :  forall A : Set, list A -> list A -> Prop
  := fun _ xs ys
       => forall x, In x xs -> In x ys.

Arguments set_list_subset {A} xs ys.

(*
  Accepts two lists, xs and ys, where xs is a
  subset of ys, and proves that every value
  that is not in ys is also not in xs.
*)
Definition set_list_subset_thm
  :  forall (A : Set) (xs ys : list A), set_list_subset xs ys -> forall z : A, ~ In z ys -> ~ In z xs
  := fun _ xs ys H z H0 (H1 : In z xs)
       => H0 (H z H1).

Arguments set_list_subset_thm {A} xs ys H z H0 H1.

Set Opaque set_list_subset_thm.

(*
  Accepts two lists of points, xs and ys, where
  xs is a subset of ys, and proves that xs
  remains a subset of ys even when we add the
  same element to both lists.
*)
Definition set_list_subset_cons
  :  forall (xs ys : list point), set_list_subset xs ys -> forall z : point, set_list_subset (z :: xs) (z :: ys)
  := fun xs ys H z w (H0 : In w (z :: xs))
       => sumbool_ind
            (fun _ => In w (z :: ys))
            (fun H1 : z = w
              => or_introl (In w ys) H1)
            (fun H1 : z <> w
              => or_ind
                   (fun H2 : z = w
                     => False_ind (In w (z :: ys)) (H1 H2))
                   (fun H2 : In w xs
                     => or_intror (z = w) (H w H2))
                   H0)
            (point_eq_dec z w).

Set Opaque set_list_subset_cons.

(*
  Proves that the tail of a list is a subset
  of the list.
*)
Definition set_list_subset_tail
  :  forall (A : Set) (x : A) (xs : list A), set_list_subset xs (x :: xs)
  := fun _ x xs y (H : In y xs)
       => or_intror (x = y) H.

Arguments set_list_subset_tail {A} x xs x0 H.

Set Opaque set_list_subset_tail.

(*
  Proves that if a point is different than every
  point in a list it is not in the list.
*)
Definition point_list_different_not_In
  :  forall (p : point) (qs : list point), point_list_different p qs -> ~ In p qs
  := fun p
       => list_rect
            (fun qs => point_list_different p qs -> ~ In p qs)
            (fun _ (H : In p nil) => H)
            (fun q qs
              (F : point_list_different p qs -> ~ In p qs)
              (H : point_list_different p (q :: qs))
              (H0 : In p (q :: qs))
              => or_ind
                   (fun H1 : q = p
                     => point_list_different_head p q qs H H1)
                   (fun H1 : In p qs
                     => F (point_list_different_tail p q qs H) H1)
                   H0).

Set Opaque point_list_different_not_In.

(*
  Proves that if a point is not in a list,
  the point does not equal the first element in
  the list.
*)
Definition point_list_not_In_head
  :  forall (p q : point) (qs : list point), ~ In p (q :: qs) -> q <> p
  := fun p q qs H
       => sumbool_ind
            (fun _ => q <> p)
            (fun H0 : q = p
              => False_ind (q <> p)
                   (H (or_introl (In p qs) H0)))
            (fun H0 : q <> p
              => H0)
            (point_eq_dec q p).

Set Opaque point_list_not_In_head.

(*
  Proves that if a point is not in a list,
  then the point is not in the tail of the
  list either.
*)
Definition point_list_not_In_tail
  :  forall (p q : point) (qs : list point), ~ In p (q :: qs) -> ~ In p qs
  := fun p q qs H (H0 : In p qs)
       => H (or_intror (q = p) H0).

Set Opaque point_list_not_In_tail.

(*
  Proves that if a point, p, is not in a list,
  qs, then p is different than every point in qs.
*)
Definition point_list_not_In_different
  :  forall (p : point) (qs : list point), ~ In p qs -> point_list_different p qs
  := fun p
       => list_rect
            (fun qs => ~ In p qs -> point_list_different p qs)
            (fun H => Forall_nil (fun q => q <> p))
            (fun q qs
              (F : ~ In p qs -> point_list_different p qs)
              (H : ~ In p (q :: qs))
              => Forall_cons q
                   (point_list_not_In_head p q qs H)
                   (F (point_list_not_In_tail p q qs H))).

Set Opaque point_list_not_In_different.

(* Proves that point_list_different is decideable. *)
Definition point_list_different_dec
  :  forall (p : point) (ps : list point), {point_list_different p ps} + {~ point_list_different p ps}
  := fun p ps
       => sumbool_rec (* over bool_dec0 (point_list_differentb p ps) *)
            (fun _ => {point_list_different p ps} + {~ point_list_different p ps})
            (fun H : point_list_differentb p ps = true
              => left (~ point_list_different p ps)
                   (proj1 (point_list_differentb_thm p ps) H))
            (fun H : point_list_differentb p ps = false
              => right (point_list_different p ps)
                   (fun H0 : point_list_different p ps
                     => diff_true_false
                          (H
                            || a = false @a by <- (proj2 (point_list_differentb_thm p ps) H0))))
            (bool_dec0 (point_list_differentb p ps)).

Set Opaque point_list_different_dec.

(*
  Proves that if a point, p, is different than
  every point in a list, qs, then p is different
  than every point in every subset of qs.
*)
Definition point_list_different_subset
  :  forall (p : point) (qs : list point), point_list_different p qs -> forall (rs : list point), set_list_subset rs qs -> point_list_different p rs
  := fun p qs H rs H0
       => point_list_not_In_different p rs
            (set_list_subset_thm rs qs H0 p
              (point_list_different_not_In p qs H)).

Set Opaque point_list_different_subset.

(*
  Proves that if a point, p, does not equal the
  first element in a list, qs, nor does it equal
  any of the remaining elements, p is not in qs.
*)
Definition point_list_not_In
  :  forall (p q : point) (qs : list point), q <> p -> ~ In p qs -> ~ In p (q :: qs)
  := fun p q qs H H0
       => or_ind 
            (fun H1 : q = p => H H1)
            (fun H1 : In p qs => H0 H1).

Set Opaque point_list_not_In.

(*
  Proves that given a point, p, and a list of
  points, ps, we can determine whether or not
  p is in ps.
*)
Definition point_list_In_dec
  :  forall (p : point) (ps : list point), {In p ps} + {~ In p ps}
  := fun p
       => list_rec
            (fun ps => {In p ps} + {~ In p ps})
            (right (In p nil)
              (fun H : In p nil => H))
            (fun q qs (F : {In p qs} + {~ In p qs})
              => sumbool_rec
                   (fun _ => {In p (q :: qs)} + {~ In p (q :: qs)})
                   (fun H : q = p
                     => left (~ In p (q :: qs))
                          (or_introl (In p qs) H))
                   (fun H : q <> p
                     => sumbool_rec
                          (fun _ => {In p (q :: qs)} + {~ In p (q :: qs)})
                          (fun H0 : In p qs
                            => left (~ In p (q :: qs))
                                 (or_intror (q = p) H0))
                          (fun H0 : ~ In p qs
                            => right (In p (q :: qs))
                                 (point_list_not_In p q qs H H0))
                          F)
                   (point_eq_dec q p)).
                          
Set Opaque point_list_In_dec.

(*
  Proves that given a point, p, and a list of
  points, ps, that contains p we can decideably
  determine whether or not p is the first element
  in ps or is contained in the tail of ps.
*)
Definition point_list_In_destr
  :  forall (p q : point) (qs : list point), In p (q :: qs) -> {q = p} + {In p qs}
  := fun p q qs H
       => sumbool_rec
            (fun _ => {q = p} + {In p qs})
            (fun H0 : q = p
              => left (In p qs) H0)
            (fun H0 : q <> p
              => sumbool_rec (* over point_list_In_dec *)
                   (fun _ => {q = p} + {In p qs})
                   (fun H1 : In p qs
                     => right (q = p) H1)
                   (fun H1 : ~ In p qs
                     => False_rec
                          ({q = p} + {In p qs})
                          (point_list_not_In p q qs H0 H1 H))
                   (point_list_In_dec p qs))
            (point_eq_dec q p).

Set Opaque point_list_In_destr.

(*
  Proves that if a point is not different than
  every point in a list, the point must be in
  the list.
*)
Definition point_list_not_different_In
  :  forall (p : point) (ps : list point), ~ point_list_different p ps -> In p ps
  := fun p ps H
       => sumbool_ind
            (fun _ => In p ps)
            (fun H0 : In p ps => H0)
            (fun H0 : ~ In p ps
              => False_ind
                   (In p ps)
                   (H (point_list_not_In_different p ps H0)))
            (point_list_In_dec p ps).

Set Opaque point_list_not_different_In.

(*
  Accepts a nonempty list of points, returns the
  first element in the list and the remaining elements.
*)
Definition point_list_destr
  :  forall ps : list point, length ps > 0 -> {x | ps = (fst x) :: (snd x)}
  := list_rect
       (fun ps => length ps > 0 -> {x | ps = (fst x) :: (snd x)})
       (fun H : 0 > 0
         => False_rec
              {x | nil = (fst x) :: (snd x)}
              (Gt.gt_irrefl 0 H))
       (fun p qs _ _
         => exist
              (fun x => (p :: qs) = (fst x) :: (snd x))
              (p, qs)
              (eq_refl (p :: qs))).

(*
  Accepts two lists, ps and qs, and returns
  true iff ps is a sublist of qs - I.E. every
  element in ps is in qs and the order in which
  the elements appear are the same.
*)
Inductive point_list_sublist : list point -> list point -> Prop
  := point_list_sublist_nil : point_list_sublist nil nil
  |  point_list_sublist_out
     : forall (p0 : point) (ps : list point) (q0 : point) (qs : list point),
       point_list_sublist (p0 :: ps) qs ->
       point_list_sublist (p0 :: ps) (q0 :: qs)
  | point_list_sublist_in
    :  forall (p0 : point) (ps : list point) (q0 : point) (qs : list point),
       p0 = q0 ->
       point_list_sublist ps qs ->
       point_list_sublist (p0 :: ps) (q0 :: qs).

(*
  Provest that if ps is a sublist of qs, then
  ps is also a subset of qs.
*)
Definition point_list_sublist_subset
  :  forall ps qs : list point, point_list_sublist ps qs -> set_list_subset ps qs
  := point_list_sublist_ind
       set_list_subset
       (fun p (H : In p nil) => False_ind (In p nil) H)
       (fun p0 ps q0 qs
         (_ : point_list_sublist (p0 :: ps) qs)
         (H0 : set_list_subset (p0 :: ps) qs)
         => fun p (H1 : In p (p0 :: ps))
              => or_intror (q0 = p) (H0 p H1))
       (fun p0 ps q0 qs
         (H0 : p0 = q0)
         (H1 : point_list_sublist ps qs)
         (H5 : set_list_subset ps qs)
         => fun p (H2 : In p (p0 :: ps))
              => or_ind
                   (fun H3 : p0 = p
                     => or_introl (In p qs)
                          (eq_sym (H0 || a = q0 @a by <- H3)))
                   (fun H3 : In p ps
                     => or_intror (q0 = p)
                          (H5 p H3))
                   H2).

(*
  point_set_list_cut
  : forall (p : point) (ps : list point),
    point_list_distinct ps -> 
    In p ps ->
    {(qs, rs) : ((list point) * (list point)) |
      ps = qs ++ (p :: rs)}

  Now we want to prove that qs and rs are
  distinct. The standard List module defines
  a predicate NoDup that is analogous to
  point_list_distinct. For this predicate, the
  module proves `NoDup (l ++ a :: l') -> NoDup
  (l ++ l')` as NoDup_remove_1. This result
  combined with a proof that `NoDup (l ++ m)
  -> NoDup l /\ NoDup m` would produce a result
  analogous to what I want.

  I'd also want to prove that `~ In p qs` and
  `~ In p rs`. The result NoDup_remove_2 proves
  `NoDup (l ++ a :: l') -> ~ In a (l ++ l')`. We
  can use proof by contradiction to prove that
  `~ In p qs /\ ~ In p rs`. If `In p qs` then, by
  In_or_app, `In p (qs ++ rs)`, which contradicts
  _. The proof is similar for rs.

  Lastly, I'd want to prove that the length
  reduced by 1 - i.e. `length ps = S (length qs
  + length rs)`. This follows from app_length
  and plus_n_Sm.

  So, the cut functipn appears to be the way to go.
  I need to prove that `forall ps,
  points_distinct ps <-> NoDup point_eq_dec ps`
  and should probably redefine points_distinct
  to align my code with the standard lib.
*)
Definition point_set_list_cut
  :  forall (p : point) (ps : list point),
     point_list_distinct ps -> 
     In p ps ->
     {x : ((list point) * (list point)) |
       ps = (fst x) ++ (p :: (snd x))}
  := fun p 
       => let T ps x := ps = (fst x) ++ (p :: (snd x)) in
          let U ps := {x : ((list point) * (list point)) | T ps x} in
          list_rect
            (fun ps => point_list_distinct ps -> In p ps -> U ps)
            (fun _ (H : False)
              => False_rect (U nil) H)
            (fun p0 ps
              (F : point_list_distinct ps -> In p ps -> U ps)
              (H : point_list_distinct (p0 :: ps))
              (H0 : In p (p0 :: ps))
              => let G
                   :  In p ps -> U ps
                   := F (point_list_distinct_tail p0 ps H) in
                 sumbool_rec (* over point_eq_dec q0 p *)
                   (fun _ => U (p0 :: ps))
                   (fun H1 : p0 = p
                     => let x := (nil, ps) in
                        exist
                          (T (p0 :: ps))
                          x
                          (eq_sym (app_nil_l (p0 :: ps))
                            || p0 :: ps = nil ++ (a :: ps) @a by <- H1))
                   (fun H1 : p0 <> p
                     => sumbool_rec (* over In p (p0 :: ps) *)
                          (fun _ => U (p0 :: ps))
                          (fun H2 : p0 = p
                            => False_rec (U (p0 :: ps)) (H1 H2))
                          (fun H2 : In p ps
                            => let (x, H3) := G H2 in
                               exist
                                 (T (p0 :: ps))
                                 (p0 :: fst x, snd x)
                                 (eq_refl (p0 :: ps)
                                   || p0 :: ps = p0 :: a @a by <- H3
                                   || p0 :: ps = a @a by <- app_comm_cons (fst x) (p :: snd x) p0))
                          (point_list_In_destr p p0 ps H0))
                   (point_eq_dec p0 p)).

(*
  TODO: This function is underspecified,
  the fact that it preserves the order of all
  elements other than p is not reflected in the
  specifications. Instead the specifications
  treat ps and qs as sets.

  I need to sharpen this specification.

  forall (p : point) (ps : list point), point_list_distinct ps -> In p ps -> {qs : list point | (forall q : point, q <> p /\ In q ps <-> In q qs) /\ point_list_distinct qs /\ S (length qs) = length ps}
*)
Definition point_set_list_remove
  :  forall (p : point) (ps : list point),
       point_list_distinct ps ->
       In p ps ->
       {qs : list point |
         (forall q : point, (q <> p /\ In q ps) <-> In q qs) /\
         length ps = S (length qs)}
  := fun p
       => let T ps qs := (forall q : point, (q <> p /\ In q ps) <-> In q qs) /\ length ps = S (length qs) in
          let U ps := {qs : list point | T ps qs} in
          list_rect
            (fun ps => point_list_distinct ps -> In p ps -> U ps)
            (fun _ (H : False)
              => False_rect (U nil) H)
            (fun q0 qs
              (F : point_list_distinct qs -> In p qs -> U qs)
              (H : point_list_distinct (q0 :: qs))
              (H0 : In p (q0 :: qs))
              => let G := F (point_list_distinct_tail q0 qs H) in
                 sumbool_rec (* over point_eq_dec q0 p *)
                   (fun _ => U (q0 :: qs))
                   (fun H1 : q0 = p
                     => exist
                          (T (q0 :: qs))
                          qs
                          (conj
                            (fun q : point
                              => conj
                                   (fun H2 : q <> p /\ In q (q0 :: qs)
                                     => or_ind
                                          (fun H3 : q0 = q
                                            => False_ind
                                                 (In q qs)
                                                 ((proj1 H2)
                                                   (eq_sym H3 || q = a @a by <- H1)))
                                          (fun H3 : In q qs => H3)
                                          (proj2 H2))
                                   (fun H2 : In q qs
                                     => conj
                                          (fun H3 : q = p
                                            => let H4
                                                 : q = q0
                                                 := H3 || q = a @a by H1 in
                                               let H5
                                                 : ~ In q0 qs 
                                                 := point_list_different_not_In q0 qs
                                                      (point_list_distinct_different q0 qs H) in
                                               let H6
                                                 :  ~ In q qs
                                                 := H5 || ~ In a qs @a by H4 in
                                               H6 H2)
                                          (or_intror (q0 = q) H2)))
                            (eq_refl (S (length qs)))))
                   (fun H1 : q0 <> p
                     => sumbool_rec (* over In p (q0 :: qs) *)
                          (fun _ => U (q0 :: qs))
                          (fun H2 : q0 = p
                            => False_rec (U (q0 :: qs)) (H1 H2))
                          (fun H2 : In p qs
                            => let (rs, H6)
                                 := G H2 in
                               exist
                                 (T (q0 :: qs))
                                 (q0 :: rs)
                                 (conj
                                   (fun (r : point)
                                     => let H3 
                                          :  (r <> p /\ In r qs) <-> In r rs
                                          := (proj1 H6) r in
                                        conj
                                          (fun H4 : r <> p /\ In r (q0 :: qs)
                                            => or_ind (* over In r (q0 :: qs) *)
                                                 (fun H5 : q0 = r
                                                   => or_introl (In r rs) H5)
                                                 (fun H5 : In r qs
                                                   => or_intror
                                                        (q0 = r)
                                                        ((proj1 H3) (conj (proj1 H4) H5)))
                                                 (proj2 H4))
                                          (fun H4 : In r (q0 :: rs)
                                            => or_ind (* over In r (q0 :: rs) *)
                                                 (fun H5 : q0 = r
                                                   => conj
                                                        (H1 || a <> p @a by <- H5)
                                                        (or_introl (In r qs) H5))
                                                 (fun H5 : In r rs
                                                   => let H7
                                                        :  r <> p /\ In r qs
                                                        := (proj2 H3) H5 in
                                                      conj
                                                        (proj1 H7)
                                                        (or_intror (q0 = r) (proj2 H7)))
                                                 H4))
                                   (eq_S (length qs) (length (q0 :: rs)) (proj2 H6))))
                          (point_list_In_destr p q0 qs H0))
                   (point_eq_dec q0 p)).

(*
  Prove that deleting an element from a list
  produces a subset.
*)
Definition point_set_list_remove_subset
  :  forall (p : point) (ps qs : list point),
     (forall q : point, (q <> p /\ In q ps) <-> In q qs) ->
     set_list_subset qs ps
  := fun p ps qs H
       => fun (q : point) (H0 : In q qs)
            => proj2 ((proj2 (H q)) H0).

Set Opaque point_set_list_remove_subset.

(*
  Accepts a line and a list of points and returns
  true iff all the ppints lie on the line.
*)
Definition points_on
  :  line -> list point -> bool
  := fun l => forallb (on l).

(*
  Accepts a list of points and asserts that they
  are collinear.
*)
Definition points_collinear
  :  list point -> Prop
  := fun ps => exists l : line, Forall (fun p => on l p = true) ps.

(*
  Accepts a line, l, and a list of points, ps,
  and proves that the points in ps are collinear
  if they all lie on l.
*)
Definition points_on_collinear
  :  forall (l : line) (ps : list point), points_on l ps = true -> points_collinear ps
  := fun l ps H
       => ex_intro
            (fun l => Forall (fun p => on l p = true) ps)
            l
            (proj2 (Forall_forall (fun p => on l p = true) ps)
              (proj1 (forallb_forall (on l) ps) H)).

(*
  Accepts a list of points and returns true iff
  they are collinear.

  Note: this function checks whether or not all
  of the points in ps lie on the line passing
  through the first two points.
*)
Definition points_collinearb
  :  forall ps : list point, point_list_distinct ps -> bool
  := list_rec
       (fun ps => point_list_distinct ps -> bool)
       (fun _ => true)
       (fun p ps _
         => list_rec
              (fun ps => point_list_distinct (cons p ps) -> bool)
              (fun _ => true)
              (fun q qs _ (H : point_list_distinct (cons p (cons q qs)))
                => let H0
                     :  q <> p
                     := point_list_differentb_head p q qs
                          (proj1
                            (andb_prop
                              (point_list_differentb p (cons q qs))
                              (point_list_distinctb (cons q qs))
                              (proj2 (point_list_distinct_thm (cons p (cons q qs))) H))) in
                   let (l, _)
                     := constructive_definite_description
                          (fun l => on l q = true /\ on l p = true)
                          (points_line_axiom q p H0) in
                   points_on l qs)
              ps).

(*
*)
Definition point_set
  :  Set
  := {ps : list point | point_list_distinct ps}.

(*
*)
Definition point_set_list
  :  point_set -> list point
  := fun ps => proj1_sig ps.

(*
*)
Definition point_set_distinct
  :  forall ps : point_set, point_list_distinct (point_set_list ps)
  := fun ps => proj2_sig ps.

(*
*)
Definition point_set_in
  :  point -> point_set -> Prop
  := fun p ps
       => In p (point_set_list ps).

(*
  Proves that we can always decide whether or
  not a point belongs to a point set.
*)
Definition point_set_in_dec
  :  forall (p : point) (ps : point_set), {point_set_in p ps} + {~ point_set_in p ps}
  := fun p ps
       => sumbool_rec
            (fun _ => {point_set_in p ps} + {~ point_set_in p ps})
            (fun H : point_set_in p ps
              => left (~ point_set_in p ps) H)
            (fun H : ~ point_set_in p ps
              => right (point_set_in p ps) H)
            (point_list_In_dec p (point_set_list ps)).

(*
*)
Definition point_set_subset
  :  point_set -> point_set -> Prop
  := fun ps qs
       => forall p : point, point_set_in p ps -> point_set_in p qs.

(*
*)
Definition point_set_disjoint
  :  point_set -> point_set -> Prop
  := fun ps qs
       => forall p : point, point_set_in p ps -> ~ point_set_in p qs.

(* Proves that point_set_disjoint is symmetrical. *)
Definition point_set_disjoint_sym
  :  forall ps qs : point_set, point_set_disjoint ps qs -> point_set_disjoint qs ps
  := fun ps qs (H : point_set_disjoint ps qs) p (H0 : point_set_in p qs) (H1 : point_set_in p ps)
       => H p H1 H0.

(*
*)
Definition point_set_eq
  :  point_set -> point_set -> Prop
  := fun ps qs
       => point_set_subset ps qs /\ point_set_subset qs ps.

(*
*)
Definition point_set_nil
  :  point_set
  := exist
       (fun ps => point_list_distinct ps)
       nil
       point_list_distinct_nil.

(*
  Accepts a point, p, and a point set, ps,
  and adds p to ps.
*)
Definition point_set_add
  :  forall (p : point) (ps : point_set), {qs : point_set | forall q : point, p = q \/ point_set_in q ps <-> point_set_in q qs}
  := fun p ps
       => sumbool_rec
            (fun _ => {qs : point_set | forall q : point, p = q \/ point_set_in q ps <-> point_set_in q qs})
            (fun H : point_list_different p (point_set_list ps)
              => let qs
                   :  point_set
                   := exist
                        point_list_distinct
                        (p :: (point_set_list ps))
                        (point_list_distinct_cons p (point_set_list ps) H (point_set_distinct ps)) in
                 exist
                   (fun rs => forall q : point, p = q \/ point_set_in q ps <-> point_set_in q rs)
                   qs
                   (fun q
                     => conj
                          (fun H0 : p = q \/ point_set_in q ps => H0)
                          (fun H0 : point_set_in q qs => H0)))
            (fun H : ~ point_list_different p (point_set_list ps)
              => exist
                   (fun rs => forall q : point, p = q \/ point_set_in q ps <-> point_set_in q rs)
                   ps
                   (fun q
                     => conj
                          (fun H0 : p = q \/ point_set_in q ps
                            => or_ind
                                 (fun H1 : p = q
                                   => point_list_not_different_In p (point_set_list ps) H
                                      || In a (point_set_list ps) @a by <- H1)
                                 (fun H1 : point_set_in q ps => H1)
                                 H0)
                          (fun H0 : point_set_in q ps
                            => or_intror (p = q) H0)))
            (point_list_different_dec p (point_set_list ps)).

(*

*)
Definition points_list_remove_distinct
  :  forall (p : point) (ps : list point), point_list_distinct ps ->
     forall qs : list point, 
     (forall q : point, (q <> p /\ In q ps) <-> In q qs) ->
     point_list_distinct qs
  := fun p
       => list_ind _
            (fun _ : point_list_distinct nil
              => list_ind _
                   (fun _ => point_list_distinct_nil)
                   (fun q0 qs _ (H : forall q : point, (q <> p /\ In q nil) <-> In q (q0 :: qs))
                     => False_ind (point_list_distinct (q0 :: qs))
                          ((proj2 (H q0))
                            (or_introl (In q qs) (eq_refl q0)))))
            (fun p0 ps
              (H : point_list_distinct ps -> forall qs, (forall q, (q <> p /\ In q qs) <-> In q qs) -> point_list_distinct qs)
              (H0 : point_list_distinct (p0 :: ps))
              => list_ind _
                   (fun _ : forall q, (q <> p /\ In q (p0 :: ps)) <-> In q nil
                     => (* we have a contradiction here as `In q nil` is false *)
                        point_list_distinct_nil)
                   (fun q0 qs
                     (_ : forall q, (q <> p /\ In q (p0 :: ps)) <-> In q qs)
                     (H1 : forall q, (q <> p /\ In q (q0 :: ps)) <-> In q (q0 :: qs))
                     => let H2
                          :  set_list_subset (q0 :: qs) (p0 :: ps)
                          := fun (q : point) (H3 : In q (q0 :: qs))
                               => proj2 ((proj2 (H1 q)) H3) in
                        point_list_distinct_cons p (q0 qs
                          (point_list_different_subset q0 ps 
                        

point_list_distinct_cons q0 qs
                          
(*
  define recursively over ps
  for the nil list let qs be nil and proof by contradiction both ways since
    1. point_set_in q nil is always false and
    2. same
  for ps = x :: xs
    cases on p = x or p <> x
      if p = x
        then return xs
          
  alt approach
  use points_distinct_remove
  cases on p in point_set_list ps = xs
    if In p xs
      then
        let ys be list ret by points_distinct_remove 
        let qs be make_point_set ys using distinctness ret by pdr.
        prove q <> p /\ point_set_in q ps -> point_set_in q qs
        by crap I need the equivalent of point_distinct_list_remove : forall p ps, distinct ps -> In p ps -> {qs | forall q, q <> p /\ In q ps <-> qs /\ distinct qs /\ S (length qs) = length ps}
          
*)
Definition point_set_remove
  :  forall (p : point) (ps : point_set), {qs : point_set | forall q : point, q <> p /\ point_set_in q ps <-> point_set_in q qs}
  := 

(*
*)
Definition make_point_set
  :  forall (ps : list point), point_list_distinct ps -> point_set
  := exist point_list_distinct ps.

(*
  Accepts a point set, ps, and asserts that ps
  is noncollinear.
*)
Definition point_set_noncollinear
  :  point_set -> Prop
  := fun ps
       => points_noncollinear (point_set_list ps).

(*
  Accepts three distinct noncollinear points
  and returns them in a point set that is
  noncollinear.
*)
Axiom point_noncollinear_triple_set
  :  forall p q r : point, distinct p q r -> noncollinear p q r -> {ps : point_set | point_set_noncollinear ps}.
(*
  := make_point_set (q :: r :: s :: nil)
       (point_list_distinct_cons q (r :: s :: nil)
         (Forall_cons
           (fun x => x <> q)
           r (s :: nil)
           (not_eq_sym (proj1 (proj2 H)))
           (Forall_cons
             (fun x => x <> q)
             s nil
             (not_eq_sym (proj2 (proj2 H)))
             (Forall_nil (fun x => x <> q))))
         (point_list_distinct_cons r (s :: nil)
           (Forall_cons
             (fun x => x <> r)
             s nil
             (not_eq_sym (proj2 (proj2 H)))
             (Forall_nil (fun x => x <> r)))
           (point_list_distinct_cons s nil
             (Forall_nil (fun x => x <> s))
             point_list_distinct_nil)))
*)

(*
informal proof sketch

if ps is a point set and p is in ps then we can get the points in ps that do not equal p, qs. and point_set_eq (point_set_add p qs) ps.

what's more if `point_set_noncollinear ps` then `point_set_noncollinear rs`

Now if ps is a triple, and p is in ps then `point_set_remove p ps` is a pair.

If `~ point_set_in p ps` and `point_set_is_pair ps` then `let (q, r) := point_set_pair ps H in distinct p q r`

If `point_set_in p ps` and `point_set_is_triple ps` and `point_set_is_noncollinear ps`
  then
    `let qs := point_set_remove p ps H in`
    since ps is a triple we can prove qs is a pair
    let (q, r) := point_set_pair in
    `point_set_eq (point_set_add p qs) ps`
    this implies that `noncollinear (point_set_add p qs)`

    prove that if qs is a pair and p is not in qs then `exist q r, point_set_eq (point_triple_set (p, q, r)) (point_set_add p qs) 

I need to define three classes of results:

  1. results about point lists, point_list_*
  2. results about point tuples
  3. results about point sets, point_set_*

point tuples fix order and size, point lists fix order, point sets fix distinctness but generalize over order and size.

A point set is a list of distinct points.

The incidence geometry axioms relate to point tuples, but most proofs are easier when I can work with point sets. Meanwhile, point sets are point lists where all the points are distinct and the operations do not care about order.

point tuple -> point set -point set remove-> point set -> point tuple

distinctness is preserved by this sequence.

noncollinearity only exists for triples and larger tuples.

if p is in a point set, ps, we have:

`point_set_eq (point_set_add p (point_set_remove p ps)) ps`

then we can rearrange tuples and maintain noncollinearity.

ps : point_set --> qs := point_set_remove p ps --> point_set_add p qs --> point_set_eq (point_set_add p qs) ps --> point_set_noncollinear (point_set_add p qs) --> point_set_is_pair qs --> let (p, q, r) := point_set_pair_add p qs --> noncollinear p q r because point_set_noncollinear ps -> noncollinear ...

thm : forall ps : point_set, point_set_is_triple ps -> point_set_noncollinear ps -> let (p, q, r) := point_set_triple ps in noncollinear p q r

and point_set_triple (point_set_add p qs) -> let (q, r) := point_set_pair qs in (p, q, r).
*)

(*
  Given a point, p, proves that there exists
  two other points, q and r, such that p, q,
  and r are distinct and noncollinear.
*)
Definition point_other_noncollinear
  :  forall p : point, exist q : point, exist r : point, distinct p q r /\ noncollinear p q r
  := ex_ind (fun q : point =>
     ex_ind (fun r : point => 
     ex_ind (
       fun (s : point) (H : distinct q r s /\ noncollinear q r s)
         => let (ps, H0)
              := point_noncollinear_triple_set q r s (proj1 H) (proj2 H) in
            sumbool_rec (* over point_set_in_dec p ps *)
              (fun H1 : point_set_in p ps
                => point_set_remove p ps H1
                       

(*
informal proof sketch

invoke collinearity_axiom to get three points q r s that are distinct and noncollinear.
either p is in the set {q r s} or its not
if p is in q r s then return the two points that p does not equal as x y.
  then q r s equals p x y and so p x y is noncollinear.
if p is not in q r s then form set {p q r}
  either {p q r} is collinear or its not
    if {p q r} is collinear then let l denote the line through p q r and form {p q s}
      either {p q s} is collinear or its not
        if {p q s} is collinear then let m denote the line through p q s
          l and m are equivalent by uniqueness in points_line_axiom p q
          hence q r s are collinear
          hence contradiction
        else return {p q s} as distinct and noncollinear
    else return {p q r} as distinct and noncollinear     
*)





(*
  TODO I forgot to factor in the fact that point sets are distinct.
*)
Definition point_set_difference_strong
  :  forall x y : point_set, {rs : point_set | forall p : point, point_set_in p x /\ ~ point_set_in p y <-> point_set_in p rs}
  := fun x y
       => let t x rs := forall p : point, point_set_in p x /\ ~ point_set_in p y <-> point_set_in p rs in
          let u x := {rs | t x rs} in
          sig_rec u
            => list_rec 
                 (fun ps => forall H : point_list_distinct ps, u (make_point_set ps H))
                 (fun H : point_list_distinct nil
                   => exist
                        (t (make_point_set nil H))
                        point_set_nil
                        (conj
                          (fun p (H0 : In p nil /\ ~ point_set_in p y)
                            => False_ind
                                 (t
                                   (make_point_set nil H)
                                   point_set_nil)
                                 (and_ind
                                   (fun (H0 : In p nil) _ => H0)
                                   H))
                          (fun H0 : point_set_in p point_set_nil
                            => False_ind
                                 (point_set_in p (make_point_set nil H) /\ ~ point_set_in p y)
                                 H0)))
                 (fun p ps F (H : point_list_distinct (p :: ps))
                   => sumbool_rec
                        (fun 

                   => exist
                        (t (make_point_set (p :: ps) H))
                        

          list_rec u
            (exist
              (t nil)
              nil
              (fun p (H : In p nil /\ ~ point_set_in p qs)
                => False_ind
                     (t nil nil)
                     (and_ind
                       (fun (H0 : In p nil) _ => H0)
                       H)))
            (fun p rs (F : u rs)
              => sumbool_rec (* over in p qs *)
                   (fun _ => u (p :: rs))
                   (fun H : point_set_in p qs
                     => let (ss, H0) := F in
                        (* H0 : {ss : point_set | forall p : point, point_set_in p rs /\ ~ point_set_in p qs -> point_set_in p ss} *)
                        exist
                          (t (p :: rs))
                          ss
                          (fun q (H1 : point_set_in q (p :: rs) /\ ~ (point_set_in q qs))
                            => or_ind
                                 (fun H2 : p = q
                                   => False_ind
                                        (point_set_in q ss)
                                        (proj2 H1
                                          (H || point_set_in a qs @a by H2)))
                                 (fun H2 : In p rs
                                   => H0 (conj H2 (proj2 H1)))
                                 (proj1 H1)))
                   (fun H : ~ point_set_in p qs
                     => let (ss, H0) := F in
                        let ts := p :: ss in
                        exist
                          (t (p :: rs))
                          ts
                          (fun q (H1 : point_set_in q (p :: rs) /\ ~ (point_set_in q qs))
                            => or_ind
                                 (fun H2 : p = q
                                   => or_inrol (In q ss) H2)
                                 (fun H2 : In p rs
                                   => or_intror
                                        (p = q)
                                        (H0 (conj H2 (proj2 H1))))
                                 (proj1 H1)))
            (point_set_list ps)

(*

(*
*)
Definition point_set_singleton
  :  forall p : point -> {ps : point_set | unique (fun q : point => point_set_is q ps) p}

(*
*)
Definition point_set_add
  :  forall (p : point) (ps : point_set), {qs : list point | point_set_eq (point_set_difference qs ps) (point_
  := fun p ps
       => 

(*
*)
Definition point_set_remove
  :  forall (p : point) (ps : point_set), point_set_in p ps -> {qs : point_set | point_set_subset qs ps /\ ~ point_set_in p qs}

(*
*)
Definition point_set_replace_collinear
  :  forall 

(*
 TODO Give me a list of the points guaranteed to exist by collinearity_axiom.

 TODO  A function that returns two other points when given a point that are proved to be different and distinct 

  : {ps : list point
      | point_list_distinct ps /\
        length ps = 3

  points_others
    : forall p : point, exists q : point, exists r : point, distinct p q r /\ noncollinear p q r

  my goal was to call the collinearity axiom to get three distinct noncollinear points q r s
  then form these in a list ps := q :: r :: s :: nil
  prove the elements were distinct using point_list_distinct_cons
  use cases over point_list_In_dec
    if p is in ps
      call points_distinct_remove to get qs where qs is distinct and doesnt contain
      in this case we can prove that p :: qs is noncollinear but we'd need to deepen our theory (points_collinear + thms).
    if p is not in ps
      we can take the first two points and use point_list_different_head and point_list_different_tail iterative to prove they are all different 

  goal
    : forall (p : point) (ps : list point) (H : point_list_distinct ps), points_noncollinear ps -> forall H0 : In p ps, let (qs, H1) := points_distinct_remove ps H p H0 in point_list_distinct (p :: qs) /\ points_noncollinear (p :: ps)

*)
 
(*
*)
Definition points_others_noncollinear
  : forall p : point, exists q : point, exists r : point, distinct p q r /\ noncollinear p q r
  := fun p
       => ex_ind (fun q : point =>
          ex_ind (fun r : point =>
          ex_ind
            (fun (s : point) (H : distinct q r s /\ noncollinear q r s)
              => let ps := (q :: r :: s :: nil) in
                 sumbool_ind (* over In p ps *)
                   (fun _ => exists x : point, exists y : point, distinct p x y /\ noncollinear p x y)
                   (fun H0 : In p ps
                     => let (qs, H1)
                          := points_distinct_remove ps 
                               (* TODO: point_list_distinct ps *)
                               p H0 in
                        let rs := p :: qs in
                        let ((x, ss), H2)
                          := point_list_destr qs
                               (lt_0_Sn 1
                                || a > 0 @a by (eq_add_S (proj1 (proj2 (proj2 H1))) : length qs = 2)) in
                        let ((y, _), H3)
                          := point_list_destr ss
                               (lt_0_Sn 0
                                || a > 0 @a by 

(*
Check (eq_add_S (length (1 :: 2 :: 3 :: nil)) 3 (eq_refl (length (0 :: 1 :: 2 :: 3 :: nil))) : length (1 :: 2 :: 3 :: nil) = 3).
*)

(*
  Proves that at least one line passes through
  each point.
*)
Definition point_line_ex
  :  forall p : point, exists l : line, on l p = true
  := fun p
       => ex_ind (fun q =>
          ex_ind (fun r =>
          ex_ind (
            fun (s : point) (H : distinct q r s /\ noncollinear q r s)
              => let qs := q :: r :: s :: nil in
                 bool_dec0
                   (fun _ => exists l : line, on l p = true)
                   (fun H : point_list_differentb p qs = true
                     => let H0
                          :  p <> q
                          := point_list_differentb_head p q (r :: s :: nil) H in
                        ex_ind
                          (fun l (H1 : unique (fun l => on l p = true /\ on l q = true) l)
                            => ex_intro
                                 (fun l => on l p = true)
                                 l
                                 (proj1 (proj1 H1)))
                          (points_line_axiom p q H0))
                   (fun H : point_list_differentb p qs = false
                     => 

Definition points_collinearb_thm
  :  forall (ps : list point) (H : point_list_distinct ps), points_collinearb ps H = true <-> points_collinear ps
  := list_rec
       (fun ps => forall H : point_list_distinct ps, points_collinearb ps H = true <-> points_collinear ps)
       (conj
         (fun H _ => 
           (*
             points_collinearb nil H= true -> points_collinear nil
             _ -> exists l, Forall _ nil
           *)
           ex_ind
             (fun (l : line) (H0 : exists m : line, l <> m)
               => ex_intro
                    (fun l => Forall (fun p => on l p = true) nil)
                    l
                    (Forall_nil (fun p => on l p = true)))
             lines_ex)
         (fun _ _ => eq_refl true))
       (fun
         (p : point)
         (ps : list point)
         (H : forall H0 : point_list_distinct, points_collinearb ps H0 = true <-> points_collinear ps)
         (H0 : point_list_distinct (p::ps))
         => conj
              (*
                points_collinearb (p :: ps) = true -> points_collinear (p :: ps)
                _ => exists l : line, Forall (fun p => on l p = true) (p :: ps)
              *)
              (*
                two cases:
                  ps is nil
                    we use fact that every point lines on a line to get l. Then use Forall_cons with Forall_nil taking care of the recursive case.
                  ps is not nil
                  ps is q::qs
                    let line be the line through p and q
                    use points_collinearb_tail to prove that q::qs is collinear
                    use ex_ind to get m the line that all q::qs is on
                    use Forall_cons 
              *)
              


              (Forall_ind
                (fun qs => points_collinearb qs = true -> points_collinear qs)
                (fun _
                  => ex_intro
                       (fun l => Forall (fun p => on l p = true) nil)
                       l
                       (Forall_nil (fun p => on l p = true)))
                (fun q qs (H0 : 
           



           (* prove that there exists a  line, then use ex instantiation to get the line and Forall_nil for this proof case. *)


(*
  := fun ps
       => conj
            (fun H : points_collinearb ps = true
              => let H0
                   :  forall p : point, In p ps -> on l p = true
                   := proj1 (forallb_forall (on l) ps) H in
                 proj2 (Forall_forall (on l) ps) H0)
            (fun H : points_collinear ps
              => let H0
                   :  forall p : point, In p ps -> on l p = true
                   := proj1 (Forall_forall (fun p => on l p = true) ps) H in
                 proj2 (forallb_forall (on l) ps) H0).
*)
End Theorems.

End Incidence.
