(*<*)
theory Containers_BNFs
  imports "HOL-Cardinals.Cardinals"
begin

(*
This theory has been tested with Isabelle2018.
It is best explored interactively by starting Isabelle/jEdit.

To download Isabelle2018 please visit

https://isabelle.in.tum.de/website-Isabelle2018/index.html

and follow the installation instruction from there.
*)

declare [[bnf_internals]]

unbundle lifting_syntax
(*>*)

section \<open>Containers are BNFs\<close>

typedecl S \<comment> \<open>A type/set of shapes.\<close>
typedecl U \<comment> \<open>A type/set of positions. Not present in the container
   formulation as they work directly with the dependent type P s
   for a fixed shape s. It can be thought of as the dependent sum
   type U = (Sum s : S. P s)\<close>

consts P :: "S \<Rightarrow> U set" \<comment> \<open>The actual assignments of positions to shapes.\<close>

text \<open>
The following type 'a F is the extension of a container.

We emulate the dependent sum type used in the containers paper using a subtype
of the independent product type. @{term "Func A B"} denotes the set of functions
from A to B. Since HOL functions are total any @{term "f \<in> Func A B"} is restricted
to return some fixed unspecified value outside of the domain @{term A}:
@{term "\<forall>x. x \<notin> A \<longrightarrow> f x = undefined"}. @{term "UNIV :: 'a set"} is the set of all
elements of type @{typ 'a}. In HOL it is necessarily non-empty.
\<close>

typedef (overloaded) 'a F = "{(s :: S, f). f \<in> Func (P s) (UNIV :: 'a set)}"
  by (auto simp: Func_def)

setup_lifting type_definition_F

text \<open>Forces a function to be @{term undefined} outside the given domain
(later this will be always @{term "P s"} for some fixed shape @{term s})\<close>

abbreviation restr where
  "restr A f x \<equiv> (if x \<in> A then f x else undefined)"

lift_definition map_F :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a F \<Rightarrow> 'b F" \<comment> \<open>Functorial action on the container extension.\<close>
  is "\<lambda>g (s, f). (s, restr (P s) (g o f))"
  by (auto simp: Func_def)

lift_definition set_F :: "'a F \<Rightarrow> 'a set" \<comment> \<open>The elemants contained in the container extension.\<close>
  is "\<lambda>(s, f). f ` P s" .

text \<open>The container extension is a BNF.\<close>

bnf "'a F"
  map: map_F
  sets: set_F
  bd: "natLeq +c card_of (UNIV :: U set)"
  subgoal by (rule ext, transfer) (auto simp: Func_def)
  subgoal by (rule ext, transfer) (auto simp: Func_def)
  subgoal by (transfer) (auto simp: Func_def)
  subgoal by (rule ext, transfer) (auto simp: Func_def)
  subgoal by (simp add: card_order_csum natLeq_card_order)
  subgoal by (simp add: cinfinite_csum natLeq_cinfinite)
  subgoal apply (transfer, clarsimp)
    apply (rule ordLeq_transitive[OF card_of_image])
    apply (rule ordLeq_transitive[OF _ ordLeq_csum2])
    apply simp_all
    done
  subgoal for R S
    apply (rule predicate2I, transfer fixing: R S, clarsimp simp: Func_def)
    subgoal for s f g
      by (rule exI[of _ "restr (P s) (\<lambda>u. (fst (f u), snd (g u)))"])
        (auto simp: relcompp_apply image_subset_iff split_beta fun_eq_iff split: if_splits)
    done
  done

text \<open>
The relator @{term rel_F} is defined internally in terms of @{term map_F} and @{term set_F}:
@{thm F.in_rel[no_vars]}.

Moreover, the above @{command bnf} command proves a wealth of useful BNF properties,
including the parametricity of most involved entities:
\begin{gather*}
@{thm F.map_transfer[no_vars]}\\
@{thm F.set_transfer[no_vars]}\\
@{thm F.rel_transfer[no_vars]}
\end{gather*}
\<close>


section \<open>Quotient Containers are BNFs\<close>

text \<open>Quotient Containers additionally allow to identify different elements
in the container extension that only differ by certain "allowed" permutations of positions.
G (for a shape s) is some set of allowed permutations (bijections) closed under composition
and inverses and containing identity.

The restriction of all functions to @{term "P s"} is necessary due to the lack of dependent types.
\<close>

axiomatization G where
  G_bij: "f \<in> G s \<Longrightarrow> bij_betw f (P s) (P s)" and
  G_id: "id \<in> G s" and
  G_comp: "f \<in> G s \<Longrightarrow> g \<in> G s \<Longrightarrow> restr (P s) (g o f) \<in> G s" and
  G_inv: "f \<in> G s \<Longrightarrow> restr (P s) (the_inv_into (P s) f) \<in> G s"

text \<open>The equivalence relation eq on the container extension
that allows to permute positions according to the functions in G.\<close>

lift_definition eq :: "'a F \<Rightarrow> 'a F \<Rightarrow> bool" is
  "\<lambda>(s1, f1). \<lambda>(s2, f2). s1 = s2 \<and> (\<exists>g \<in> G s1. f1 = restr (P s1) (f2 o g))" .

lemma eq_refl[simp]: "eq x x"
  by transfer (auto simp: fun_eq_iff Func_def G_id intro!: bexI[of _ id])

lemma eq_sym: "eq x y \<Longrightarrow> eq y x"
  apply (transfer; clarsimp)
  subgoal for s f1 f2
    apply (frule G_bij)
    apply (auto simp: fun_eq_iff Func_def G_inv
      f_the_inv_into_f_bij_betw bij_betw_def the_inv_into_into
      intro!: bexI[of _ "restr (P s) (the_inv_into (P s) f2)"])
    done
  done

lemma eq_trans: "eq x y \<Longrightarrow> eq y z \<Longrightarrow> eq x z"
  apply (transfer; clarsimp)
  subgoal for s f1 f g
    apply (frule G_bij)
    apply (auto simp: fun_eq_iff Func_def G_comp
      f_the_inv_into_f_bij_betw bij_betw_def the_inv_into_into
      intro!: bexI[of _ "restr (P s) (g o f)"])
    done
  done

text \<open>The extension of a quotient container is the container extension
  @{typ "'a F"}, quotiented by @{term eq}\<close>

quotient_type (overloaded) 'a Q = "'a F" / eq
  by (intro equivpI reflpI sympI transpI eq_refl | elim eq_sym eq_trans | assumption)+

lift_definition map_Q :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Q \<Rightarrow> 'b Q" \<comment> \<open>Functorial action on the quotient container
    extension simply lifted from the container extension.\<close>
  is "map_F"
  subgoal for g f1 f2
    supply F.map_transfer[transfer_rule del]
    apply (transfer fixing: g, clarsimp)
    subgoal for s f1 f2
      apply (frule G_bij)
      apply (auto simp: fun_eq_iff Func_def bij_betw_def intro!: bexI[of _ f2])
      done
    done
  done

lift_definition set_Q :: "'a Q \<Rightarrow> 'a set" \<comment> \<open>The set of elements in the quotient container
    extension are the ones in the underlying container extension (equivalent container extension
    elements have equal sets of elements).\<close>
  is set_F
  subgoal for f1 f2
    supply F.set_transfer[transfer_rule del]
    apply (transfer, clarsimp)
    subgoal for s g f
    apply (frule G_bij)
      apply (auto simp: Func_def image_iff bij_betw_def intro: bexI[of _ "f _"])
      apply (metis image_iff)
      done
    done
  done

text \<open>The quotient container extension is a BNF.\<close>

bnf "'a Q"
  map: map_Q
  sets: set_Q
  bd: "natLeq +c card_of (UNIV :: U set)"
  subgoal by (rule ext, transfer) (auto simp: F.map_id)
  subgoal by (rule ext, transfer) (auto simp: F.map_comp)
  subgoal by (transfer) (auto cong: F.map_cong)
  subgoal by (rule ext, transfer) (auto simp: F.set_map)
  subgoal by (simp add: card_order_csum natLeq_card_order)
  subgoal by (simp add: cinfinite_csum natLeq_cinfinite)
  subgoal by (transfer, clarsimp, rule F.set_bd)
  subgoal for R S
    apply (rule predicate2I, transfer fixing: R S, clarsimp simp: Func_def)
    supply F.map_transfer[transfer_rule del] F.set_transfer[transfer_rule del]
    apply (transfer fixing: R S; clarsimp)
    subgoal for f1 s f2 f3 l r g1 g2 g3 g4
      apply (rule exI[of _ "restr (P s) (\<lambda>u. (fst (l u), snd (r (the_inv_into (P s) g3 (g2 u)))))"])
      apply (auto simp: relcompp_apply image_subset_iff split_beta fun_eq_iff Func_def
        split: if_splits)
       apply (smt G_bij bij_betw_def f_the_inv_into_f image_eqI the_inv_into_onto)
      apply (rule bexI[of _ "restr (P s) (g4 o restr (P s) (restr (P s) (the_inv_into (P s) g3) o g2))"], clarsimp)
      apply (metis G_bij bij_betw_def image_eqI the_inv_into_onto)
      apply (intro G_comp G_inv; assumption)
      done
    done
  done

text \<open>
As before relator @{term rel_Q} is defined internally in terms of @{term map_Q} and @{term set_Q}:
@{thm Q.in_rel[no_vars]}.

Moreover, the above @{command bnf} command proves a wealth of useful BNF properties,
including the parametricity of most involved entities:
\begin{gather*}
@{thm Q.map_transfer[no_vars]}\\
@{thm Q.set_transfer[no_vars]}\\
@{thm Q.rel_transfer[no_vars]}
\end{gather*}
\<close>

(*<*)
end
(*>*)