// I hope you like spaghetti code

// This code is a bit of a mess, at least in a small part due to the fact that we switch between
// four distinct representations for expressions:
// * Raw strings (for input only)
// * An inductive representation (or the poor man's version thereof, courtesy of JS)
// * The same sort-of inductive representation serialized as a string
// * The HTML representation (the node you actually see)
//   HTML nodes actually store the serialized inductive representation of their contents via their
//   `data-expr` attribute.

// DOM nodes
var proof               = document.getElementById("proof");
var proof_top           = document.getElementById("proof-top");
var premises_holder     = document.getElementById("premises");
var input_panel         = document.getElementById("input-panel");
var input_panel_title   = document.getElementById("input-panel-title");
var input_panel_field   = document.getElementById("input-panel-field");
var input_panel_confirm = document.getElementById("input-panel-confirm");
var input_panel_error   = document.getElementById("input-panel-error-message");
var intro_rules_holder  = document.getElementById("intro-rules-holder");
var level_panel         = document.getElementById("level-panel");
var help_panel          = document.getElementById("help-panel");
var focus               = document.getElementById("focus");
var drag_box            = document.getElementById("drag-box");
var intro_rules         = document.getElementById("intro-rules");
var elim_rules          = document.getElementById("elim-rules");
var special_rules       = document.getElementById("special-rules");
var done_message        = document.getElementById("done-message");
var change_button       = document.getElementById("change-button");
var as_premise_button   = document.getElementById("as-premise-button");
var add_premise_button  = document.getElementById("add-premise-button");
var level_gallery       = document.getElementById("level-gallery");


// Configuration
var exercise_mode = true;
var current_exercise = 0; // overridden when loading persistent data
const version = 2; // for import/export


// Peano axioms are implemented as context-dependent pattern-matching rules
// (see matches_* functions and apply_axiom_rule)


// Axiom pattern matchers (check if focused node matches an axiom instance)
function matches_add_zero(e) {
  return e.type === "Eq" && ((e.t1.type === "Add" && e.t1.t2.type === "Zero")
                          || (e.t2.type === "Add" && e.t2.t2.type === "Zero"));
}
function matches_add_succ(e) {
  return e.type === "Eq" && ((e.t1.type === "Add" && e.t1.t2.type === "Succ")
                          || (e.t2.type === "Add" && e.t2.t2.type === "Succ"));
}
function matches_succ_cancel(e) {
  return e.type === "Eq" && e.t1.type === "Succ" && e.t2.type === "Succ";
}
function matches_mul_zero(e) {
  return e.type === "Eq" && ((e.t1.type === "Mul" && e.t1.t2.type === "Zero")
                          || (e.t2.type === "Mul" && e.t2.t2.type === "Zero"));
}
function matches_mul_succ(e) {
  return e.type === "Eq" && ((e.t1.type === "Mul" && e.t1.t2.type === "Succ")
                          || (e.t2.type === "Mul" && e.t2.t2.type === "Succ"));
}
function matches_succ_inj(e) {
  return e.type === "Eq";
}
function matches_zero_neq_succ(e) {
  return e.type === "Not" && e.e.type === "Eq"
    && e.e.t1.type === "Succ" && e.e.t2.type === "Zero";
}
function matches_lt_zero(e) {
  return e.type === "Not" && e.e.type === "Lt" && e.e.t2.type === "Zero";
}
function matches_lt_succ(e) {
  return e.type === "Iff" && e.e1.type === "Lt" && e.e1.t2.type === "Succ"
    && e.e2.type === "Or" && e.e2.e1.type === "Lt" && e.e2.e2.type === "Eq"
    && expr_equal(e.e1.t1, e.e2.e1.t1) && expr_equal(e.e1.t2.t, e.e2.e1.t2)
    && expr_equal(e.e1.t1, e.e2.e2.t1) && expr_equal(e.e1.t2.t, e.e2.e2.t2);
}
function matches_eq_intro(e) {
  return e.type === "Eq" && expr_equal(e.t1, e.t2);
}


// Exercises

// 1. m = n → m = n + 0 (→-intro, add-zero, premise)
const exercise_1 = '{"type":"Impl","e1":{"type":"Eq","t1":{"type":"Var","name":"m"},"t2":{"type":"Var","name":"n"}},"e2":{"type":"Eq","t1":{"type":"Var","name":"m"},"t2":{"type":"Add","t1":{"type":"Var","name":"n"},"t2":{"type":"Zero"}}}}';

// 2. m = n → n = m (→-intro, =-elim, =-intro)
const exercise_2 = '{"type":"Impl","e1":{"type":"Eq","t1":{"type":"Var","name":"m"},"t2":{"type":"Var","name":"n"}},"e2":{"type":"Eq","t1":{"type":"Var","name":"n"},"t2":{"type":"Var","name":"m"}}}';

// 3. m = n → ↑m = ↑n (→-intro, =-elim, =-intro)
const exercise_3 = '{"type":"Impl","e1":{"type":"Eq","t1":{"type":"Var","name":"m"},"t2":{"type":"Var","name":"n"}},"e2":{"type":"Eq","t1":{"type":"Succ","t":{"type":"Var","name":"m"}},"t2":{"type":"Succ","t":{"type":"Var","name":"n"}}}}';

// 4. ∃m. ↑m + ↑0 = ↑↑↑0 (∃-intro, add-succ, ..., add-zero, =-intro)
const exercise_4 = '{"type":"Exists","bound_var":"m","e":{"type":"Eq","t1":{"type":"Add","t1":{"type":"Succ", "t":{"type":"Var","name":"m"}},"t2":{"type":"Succ","t":{"type":"Zero"}}},"t2":{"type":"Succ","t":{"type":"Succ","t":{"type":"Succ","t":{"type":"Zero"}}}}}}';

// 5. ¬(∀m. m < 0) (¬-intro, →-intro, ¬-elim, ∀-elim, lt-zero)
const exercise_5 = '{"type":"Not","e":{"type":"Forall","bound_var":"m","e":{"type":"Lt","t1":{"type":"Var","name":"m"},"t2":{"type":"Zero"}}}}';

// 6. ¬(∃m. m < 0) (¬-intro, →-intro, ∃-elim, ∀-intro, ¬-elim, lt-zero)
const exercise_6 = '{"type":"Not","e":{"type":"Exists","bound_var":"m","e":{"type":"Lt","t1":{"type":"Var","name":"m"},"t2":{"type":"Zero"}}}}';

// 7. m = n → m = n + 0 (→-intro, add-zero, premise)
const exercise_7 = '{"type":"Impl","e1":{"type":"Eq","t1":{"type":"Var","name":"m"},"t2":{"type":"Var","name":"n"}},"e2":{"type":"Eq","t1":{"type":"Var","name":"m"},"t2":{"type":"Add","t1":{"type":"Zero"},"t2":{"type":"Var","name":"n"}}}}';

function make_exercise(objective, premises) {
  return {objective: objective, premises: premises, save_data: null};
}

var exercises_data = [
  make_exercise(exercise_1, []), make_exercise(exercise_2, []),
  make_exercise(exercise_3, []), make_exercise(exercise_4, []),
  make_exercise(exercise_5, []), make_exercise(exercise_6, []),
  make_exercise(exercise_7, []),
];


// Conversions between different representations
// String -> Inductive <-> Serialized inductive
//               \-------> HTML
// Serializing/deserializing done via JSON.stringify/JSON.parse
// String to inductive done in a later section (see tokenize and parse_input_field functions)
function tree_to_html(tree) { // Inductive -> HTML
  function tree_to_html_aux(tree) {
    switch (tree.type) {
      case "False": return `<div class='expr'>⊥</div>`;
      case "Not"  : return `<div class='expr'> ¬${tree_to_html_aux(tree.e)} </div>`;
      case "And":
        return `<div class='expr'>${tree_to_html_aux(tree.e1)} ∧ ${tree_to_html_aux(tree.e2)}</div>`;
      case "Or":
        return `<div class='expr'>${tree_to_html_aux(tree.e1)} ∨ ${tree_to_html_aux(tree.e2)}</div>`;
      case "Impl":
        return `<div class='expr'>${tree_to_html_aux(tree.e1)} → ${tree_to_html_aux(tree.e2)}</div>`;
      case "Iff":
        return `<div class='expr'>${tree_to_html_aux(tree.e1)} ↔ ${tree_to_html_aux(tree.e2)}</div>`;
      case "Forall":
        return `<div class='expr'>∀${tree.bound_var}.${tree_to_html_aux(tree.e)}</div>`;
      case "Exists":
        return `<div class='expr'>∃${tree.bound_var}.${tree_to_html_aux(tree.e)}</div>`;
      case "Eq":
        return `<div class='expr'>${tree_to_html_aux(tree.t1)} = ${tree_to_html_aux(tree.t2)}</div>`;
      case "Lt":
        return `<div class='expr'>${tree_to_html_aux(tree.t1)} &lt; ${tree_to_html_aux(tree.t2)}</div>`;
      case "Add":
        return `<div class='expr'>${tree_to_html_aux(tree.t1)} + ${tree_to_html_aux(tree.t2)}</div>`;
      case "Mul":
        return `<div class='expr'>${tree_to_html_aux(tree.t1)} * ${tree_to_html_aux(tree.t2)}</div>`;
      case "Succ": return `<div class='expr'>↑${tree_to_html_aux(tree.t)}</div>`;
      case "Zero": return `<div class='expr'>0</div>`;
      case "Var" : return `<div class='expr'>${tree.name}</div>`;
      default: return null;
    }
  }

  switch (tree.type) { // First level is not wrapped in an expr node
    case "False" : return `⊥`;
    case "Not"   : return ` ¬${tree_to_html_aux(tree.e)}`;
    case "And"   : return `${tree_to_html_aux(tree.e1)} ∧ ${tree_to_html_aux(tree.e2)}`;
    case "Or"    : return `${tree_to_html_aux(tree.e1)} ∨ ${tree_to_html_aux(tree.e2)}`;
    case "Impl"  : return `${tree_to_html_aux(tree.e1)} → ${tree_to_html_aux(tree.e2)}`;
    case "Iff"   : return `${tree_to_html_aux(tree.e1)} ↔ ${tree_to_html_aux(tree.e2)}`;
    case "Forall": return `∀${tree.bound_var}.${tree_to_html_aux(tree.e)}`;
    case "Exists": return `∃${tree.bound_var}.${tree_to_html_aux(tree.e)}`;
    case "Eq"    : return `${tree_to_html_aux(tree.t1)} = ${tree_to_html_aux(tree.t2)}`;
    case "Lt"    : return `${tree_to_html_aux(tree.t1)} &lt; ${tree_to_html_aux(tree.t2)}`;
    case "Add"   : return `${tree_to_html_aux(tree.t1)} + ${tree_to_html_aux(tree.t2)}`;
    case "Mul"   : return `${tree_to_html_aux(tree.t1)} * ${tree_to_html_aux(tree.t2)}`;
    case "Succ"  : return `↑${tree_to_html_aux(tree.t)}`;
    case "Zero"  : return `0`;
    case "Var"   : return `${tree.name}`;
    default: return null;
  }
}


// Proof status
function check_whether_proof_done() {
  if (proof.children[0].children[2].children[0].classList.contains("known")) {
    drag_box.classList.add("known");
    level_gallery.children[current_exercise].classList.add("known");
  } else {
    drag_box.classList.remove("known");
    level_gallery.children[current_exercise].classList.remove("known");
  }
}

function update_status_of_lower_tree(level) {
  function are_all_immediately_above_known(level) {
    let above_hyps = level.parentNode.parentNode.children[0];
    if (above_hyps) {
      for (h of above_hyps.children) {
        if (!h.children[2].children[0].classList.contains("known")) {
          return false;
        }
      }
      return true;
    }
  }

  if (level.classList.contains("expr") && are_all_immediately_above_known(level)) {
    level.classList.add("known");
    if (level.parentNode.parentNode.parentNode.parentNode.id != "proof-top") {
      update_status_of_lower_tree(
        level.parentNode.parentNode.parentNode.parentNode.children[2].children[0]
      );
    }
  }
}


// Focus and highlight management
function highlight_cause(node) {
  let known = node.known;
  if (known) {
    known.classList.add("known-cause-for-node");
  }
}

function set_focus(source) {
  if (focus && focus !== source) {
    let known = focus.known;
    if (known) {
      known.classList.remove("known-cause-for-node");
    }
    focus.removeAttribute("id");
  }

  focus = source;
  focus.setAttribute("id", "focus");
  update_contextual_actions();
  update_premises();
  update_known(focus);

  highlight_cause(focus);
}


// Level management
function populate_level_selector() { // Dynamically, using exercises_data
  for (let i = 0; i < exercises_data.length; i++) {
    level_gallery.insertAdjacentHTML(
      "beforeend",
      `<div class="gallery-item" onclick="switch_to_level(${i})"><div class=gallery-title>Ex. ${i+1}</div><hr/><div class=gallery-description>${tree_to_html(JSON.parse(exercises_data[i].objective))}</div></div>`
    );
  }
  for (let i = 0; i < 3; i++) {
    level_gallery.insertAdjacentHTML(
      "beforeend",
      `<div class=gallery-i-wish-i-didnt-have-to-resort-to-this-dirty-hack></div>`
    );
  }
}

function save_level_aux(node) {
  let sep = node.parentNode.parentNode.children[1];
  let above = node.parentNode.parentNode.children[0];

  function get_nth_above_child_expr(n) {
    return above.children[n].children[2].children[0].getAttribute("data-expr");
  }

  function gen_subactions() {
    let subactions = [];
    for (c of above.children) {
      subactions.push(save_level_aux(c.children[2].children[0]));
    }
    return subactions;
  }

  if (sep.innerHTML != "") { // The rule that was used is "physically" printed on the separation bar
    switch (sep.children[1].innerHTML) {
      case "↔-elim-l":        return { type: sep.children[1].innerHTML, arg: get_nth_above_child_expr(1), subactions: gen_subactions(), };
      case "↔-elim-r":        return { type: sep.children[1].innerHTML, arg: get_nth_above_child_expr(1), subactions: gen_subactions(), };
      case "∧-elim-l":        return { type: sep.children[1].innerHTML, arg: JSON.stringify(JSON.parse(get_nth_above_child_expr(0)).e2), subactions: gen_subactions(), };
      case "∧-elim-r":        return { type: sep.children[1].innerHTML, arg: JSON.stringify(JSON.parse(get_nth_above_child_expr(0)).e1), subactions: gen_subactions(), };
      case "∨-elim":          return { type: sep.children[1].innerHTML, arg: get_nth_above_child_expr(0), subactions: gen_subactions(), };
      case "DNE (classical)": return { type: sep.children[1].innerHTML, subactions: gen_subactions(), };
      case "⊥-elim":          return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "→-elim":          return { type: sep.children[1].innerHTML, arg: get_nth_above_child_expr(0), subactions: gen_subactions() };
      case "¬-elim":          return { type: sep.children[1].innerHTML, arg: get_nth_above_child_expr(0), subactions: gen_subactions() };
      case "¬-intro":         return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "∧-intro":         return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "∨-intro-l":       return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "∨-intro-r":       return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "→-intro":         return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "↔-intro":         return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      // TODO doublecheck
      case "∀-intro":         return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "∀-elim":          return { type: sep.children[1].innerHTML, arg: get_nth_above_child_expr(0), subactions: gen_subactions() };
      case "∃-intro":         return { type: sep.children[1].innerHTML, arg: get_nth_above_child_expr(0), subactions: gen_subactions() };
      case "∃-elim":          return { type: sep.children[1].innerHTML, arg: get_nth_above_child_expr(0), subactions: gen_subactions() };
      case "succ-inj":        return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "zero≠succ":       return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "add-zero":        return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "add-succ":        return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "succ-cancel":    return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "mul-zero":        return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "mul-succ":        return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "lt-zero":         return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "lt-succ":         return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "induction":       return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "=-intro":         return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "=-elim":          return { type: sep.children[1].innerHTML, arg: get_nth_above_child_expr(0), subactions: gen_subactions() };
    }
  } else {
    return { type: "done" };
  }
}

function save_current_level() {
  exercises_data[current_exercise].save_data =
    save_level_aux(proof.children[0].children[2].children[0]);
}

// Disgusting way of doing error checking. POSIX does the same so oh well.
let rebuild_level_failed = false;
function rebuild_level_aux(actions) {
  // TODO double check
  function is_legal_move(expr, move, arg) { // Never trust students
    let legal_moves = [
      "↔-elim-l", "↔-elim-r", "∧-elim-l", "∧-elim-r", "∨-elim", "DNE (classical)", "⊥-elim",
      "→-elim", "∀-elim", "∃-elim",
      "=-elim"
    ];

    switch (expr.type) {
      case "Var"   : break;
      case "False" : legal_moves.push("¬-elim"); break;
      case "Not"   : legal_moves.push("¬-intro"); break;
      case "And"   : legal_moves.push("∧-intro"); break;
      case "Or"    : legal_moves.push("∨-intro-l", "∨-intro-r"); break;
      case "Impl"  : legal_moves.push("→-intro"); break;
      case "Iff"   : legal_moves.push("↔-intro"); break;
      case "Forall": legal_moves.push("∀-intro", "induction"); break;
      case "Exists": legal_moves.push("∃-intro"); break;
    }

    // Axiom rules: only legal when the pattern matches
    if (matches_eq_intro(expr))      legal_moves.push("=-intro");
    if (matches_add_zero(expr))      legal_moves.push("add-zero");
    if (matches_add_succ(expr))      legal_moves.push("add-succ");
    if (matches_succ_cancel(expr))   legal_moves.push("succ-cancel");
    if (matches_mul_zero(expr))      legal_moves.push("mul-zero");
    if (matches_mul_succ(expr))      legal_moves.push("mul-succ");
    if (matches_succ_inj(expr))      legal_moves.push("succ-inj");
    if (matches_zero_neq_succ(expr)) legal_moves.push("zero≠succ");
    if (matches_lt_zero(expr))       legal_moves.push("lt-zero");
    if (matches_lt_succ(expr))       legal_moves.push("lt-succ");

    if (!legal_moves.includes(move)) {
      return false;
    }

    // TODO forall, exists
    // This checks that the arg is present if required and has the right type
    if (["↔-elim-l", "↔-elim-r", "∧-elim-l", "∧-elim-r", "→-elim", "¬-elim"].includes(move)) {
      if (!arg) {
        return false;
      } else {
        return true;
      }
    } else if (move === "∨-elim") {
      if (!arg || !arg.type || arg.type != "Or") { // This condition is revolting but that's JS
        return false;
      } else {
        return true;
      }
    } else if (move === "=-elim") {
      if (!arg || !arg.type || arg.type != "Eq") {
        return false;
      } else {
        return true;
      }
    } else if (move === "∃-elim") {
      if (!arg || !arg.type || arg.type != "Exists") {
        return false;
      } else {
        return true;
      }
    } else if (move === "∀-elim") {
      if (!arg || !arg.type || arg.type != "Forall") {
        return false;
      } else {
        return true;
      }
    } else if (move === "∃-intro") {
      if (!arg) {
        return false;
      } else {
        return true;
      }
    } else {
      return true;
    }
  }

  function rebuild_children() {
    if (actions.subactions.length > 0) {
      let curr = focus;
      rebuild_level_aux(actions.subactions[0]);
      set_focus(curr);
      for (let i = 0; i < actions.subactions.length - 1; i++) {
        curr = focus.parentNode.parentNode.parentNode.children[i+1].children[2].children[0];
        set_focus(curr);
        rebuild_level_aux(actions.subactions[i+1]);
        set_focus(curr);
      }
    }
  }

  if (actions.type == "done" || focus.known) { return; }
  if (
    actions.type
    && !is_legal_move(JSON.parse(focus.getAttribute("data-expr")), actions.type, actions.arg ? JSON.parse(actions.arg) : null)
  ) {
    rebuild_level_failed = true;
    return;
  }

  let expr = JSON.parse(focus.getAttribute("data-expr"));
  switch (actions.type) {
    case "↔-elim-l":        apply_rule("↔-elim-l", iff_elim_l, JSON.parse(actions.arg)); rebuild_children(); break;
    case "↔-elim-r":        apply_rule("↔-elim-r", iff_elim_r, JSON.parse(actions.arg)); rebuild_children(); break;
    case "∧-elim-l":        apply_rule("∧-elim-l", and_elim_l, JSON.parse(actions.arg)); rebuild_children(); break;
    case "∧-elim-r":        apply_rule("∧-elim-r", and_elim_r, JSON.parse(actions.arg)); rebuild_children(); break;
    case "∨-elim":          apply_rule("∨-elim", or_elim, JSON.parse(actions.arg)); rebuild_children(); break;
    case "DNE (classical)": apply_rule("DNE (classical)", dne); rebuild_children(); break;
    case "⊥-elim":          apply_rule("⊥-elim", false_elim); rebuild_children(); break;
    case "→-elim":          apply_rule("→-elim", impl_elim, JSON.parse(actions.arg)); rebuild_children(); break;
    case "¬-elim":          apply_rule("¬-elim", not_elim, JSON.parse(actions.arg)); rebuild_children(); break;
    // TODO
    case "∀-elim":          apply_rule("∀-elim", forall_elim, JSON.parse(actions.arg)); rebuild_children(); break;
    case "∃-elim":          apply_rule("∃-elim", exists_elim, JSON.parse(actions.arg)); rebuild_children(); break;
    case "¬-intro":         apply_rule("¬-intro", not_intro); rebuild_children(); break;
    case "∧-intro":         apply_rule("∧-intro", and_intro); rebuild_children(); break;
    case "∨-intro-l":       apply_rule("∨-intro-l", or_intro_l); rebuild_children(); break;
    case "∨-intro-r":       apply_rule("∨-intro-r", or_intro_r); rebuild_children(); break;
    case "→-intro":         apply_rule("→-intro", impl_intro); rebuild_children(); break;
    case "↔-intro":         apply_rule("↔-intro", iff_intro); rebuild_children(); break;
    // TODO
    case "∀-intro":         apply_rule("∀-intro", forall_intro, true); rebuild_children(); break;
    case "∃-intro":         apply_rule("∃-intro", exists_intro_rebuild, JSON.parse(actions.arg)); rebuild_children(); break;
    case "succ-inj":        apply_rule("succ-inj", succ_inj_rule); rebuild_children(); break;
    case "zero≠succ":       apply_axiom_rule("zero≠succ"); break;
    case "add-zero":        apply_rule("add-zero", add_zero_rule); rebuild_children(); break;
    case "add-succ":        apply_rule("add-succ", add_succ_rule); rebuild_children(); break;
    case "succ-cancel":    apply_rule("succ-cancel", succ_cancel_rule); rebuild_children(); break;
    case "mul-zero":        apply_rule("mul-zero", mul_zero_rule); rebuild_children(); break;
    case "mul-succ":        apply_rule("mul-succ", mul_succ_rule); rebuild_children(); break;
    case "lt-zero":         apply_axiom_rule("lt-zero"); break;
    case "lt-succ":         apply_axiom_rule("lt-succ"); break;
    case "induction":       apply_rule("induction", peano_induction); rebuild_children(); break;
    case "=-intro":         apply_axiom_rule("=-intro"); break;
    case "=-elim":          apply_rule("=-elim", eq_elim, JSON.parse(actions.arg)); rebuild_children(); break;
    case "done": break;
    default: return null;
  }
}

const exercise_style = document.createElement("style");
exercise_style.innerHTML = ".remove-cross { display: none !important; }";
document.head.appendChild(exercise_style);
function setup() {
  const concl = exercises_data[current_exercise].objective;
  const premises = exercises_data[current_exercise].premises;

  proof.children[0].children[2].children[0].innerHTML = tree_to_html(JSON.parse(concl));
  proof.children[0].children[2].children[0].setAttribute("data-expr", concl);
  set_focus(proof.children[0].children[2].children[0]);
  clear_above(focus);

  premises_holder.innerHTML = "";
  for (p of premises) {
    insert_premise(JSON.parse(p), true);
  }

  if (exercise_mode) {
    change_button.style.display = "none";
    as_premise_button.style.display = "none";
    add_premise_button.style.display = "none";
    exercise_style.disabled = false;
  } else {
    change_button.style.display = "block";
    as_premise_button.style.display = "block";
    add_premise_button.style.display = "flex";
    exercise_style.disabled = true;
  }
}

function rebuild_level(actions) {
  rebuild_level_failed = false;
  setup();
  rebuild_level_aux(actions);
  if (rebuild_level_failed) {
    setup();
  }
  set_focus(proof.children[0].children[2].children[0]);
}

function load_current_level() {
  const data = exercises_data[current_exercise].save_data;
  setup();
  if (data) {
    rebuild_level(data);
  } else {
    setup();
  }
  check_whether_proof_done();
}


// Level panel
var is_level_panel_open = false; // Yay, global state
function open_level_panel() {
  is_level_panel_open = true;
  level_panel.style.display = "block";
  document.documentElement.style.overflow = "hidden";
  document.body.scroll = "no";
  level_panel.focus();
}

function close_level_panel() {
  is_level_panel_open = false;
  level_panel.style.display = "none";
  document.documentElement.style.overflow = "scroll";
  document.body.scroll = "yes";
}

function close_level_panel_click_handler(event, element) {
  if (event.target == element) {
    close_level_panel();
  } else {
    event.stopPropagation();
  }
}

function switch_to_level(n) {
  save_current_level();
  persistent_save();
  current_exercise = n;
  load_current_level();
  close_level_panel();
}


// Help panel
var is_help_panel_open = false; // Yay, more global state
function open_help_panel() {
  is_help_panel_open = true;
  help_panel.style.display = "block";
  document.documentElement.style.overflow = "hidden";
  document.body.scroll = "no";
  help_panel.focus();
}

function close_help_panel() {
  is_help_panel_open = false;
  help_panel.style.display = "none";
  document.documentElement.style.overflow = "scroll";
  document.body.scroll = "yes";
}

function close_help_panel_click_handler(event, element) {
  if (event.target == element) {
    close_help_panel();
  } else {
    event.stopPropagation();
  }
}


// Persistent data management
function persistent_save() {
  save_current_level();
  let exercises_saves = [];
  let exercises_status = [];
  for (let i = 0; i < exercises_data.length; i++) {
    exercises_saves.push(exercises_data[i].save_data);
    exercises_status.push(level_gallery.children[i].classList.contains("known"));
  }
  localStorage.setItem(
    "persistent_state",
    JSON.stringify({
      version: version, current_exercise: current_exercise, exercises_data: exercises_saves,
      exercises_status: exercises_status,
    })
  );
}
window.addEventListener("beforeunload", () => { persistent_save(); });
window.addEventListener("pagehide", () => { persistent_save(); });

function persistent_clear() { // For manual use only
  const saved = localStorage.removeItem("persistent_state");
  persistent_load();
}

function persistent_load() {
  const saved = localStorage.getItem("persistent_state");
  if (saved) {
    state = JSON.parse(saved);
    if (state.version === version) {
      current_exercise = state.current_exercise;
      for (let i = 0; i < exercises_data.length; i++) {
        exercises_data[i].save_data = state.exercises_data[i];
        if (state.exercises_status[i]) {
          level_gallery.children[i].classList.add("known");
        }
      }
    }
  }
}


// Import/export
function import_data() {
  // This is all quite silly, but I'm not the one writing the standards
  document.getElementById('file-input').click();
}
document.getElementById('file-input').addEventListener('change', function(e) {
  const file = e.target.files[0];
  if (!file) return;

  const reader = new FileReader();
  reader.onload = function(e) {
    const contents = e.target.result;
    localStorage.setItem("persistent_state", contents);
    persistent_load();
    load_current_level();
  };
  reader.readAsText(file);
});

function export_data() {
  save_current_level();
  persistent_save(); // probably not necessary
  let data = localStorage.getItem("persistent_state");
  const blob = new Blob([data], { type: "application/json" });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = "logic.cool";
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
}


// Expression input: parsing
const Expression = { // Expression constructors
  EAnd:    (e1, e2)  => ({ type: "And", e1, e2 }),
  EOr:     (e1, e2)  => ({ type: "Or", e1, e2 }),
  EImpl:   (e1, e2)  => ({ type: "Impl", e1, e2 }),
  EIff:    (e1, e2)  => ({ type: "Iff", e1, e2 }),
  ENot:    (e)       => ({ type: "Not", e }),
  EFalse:  ()        => ({ type: "False" }),
  EForall: (bound_var, e) => ({ type: "Forall", bound_var, e }),
  EExists: (bound_var, e) => ({ type: "Exists", bound_var, e }),
  TLt:     (t1, t2)  => ({ type: "Lt", t1, t2 }),
  TEq:     (t1, t2)  => ({ type: "Eq", t1, t2 }),
  TAdd:    (t1, t2)  => ({ type: "Add", t1, t2 }),
  TMul:    (t1, t2)  => ({ type: "Mul", t1, t2 }),
  TSucc:   (t)       => ({ type: "Succ", t }),
  TZero:   ()        => ({ type: "Zero" }),
  TVar:    (name)    => ({ type: "Var", name }),
};
const Connective = {
  AND: "∧", OR: "∨", IMPL: "→", IFF: "↔", NOT: "¬", FALSE: "⊥",
  FORALL: "∀", EXISTS: "∃", SUCC: "↑", ZERO: "0", ADD: "+", MUL: "*",
  EQUALS: "=", LT: "<", DOT: "."
};

function tokenize(input) {
  let tokens = [];
  let scratchpad = "";
  let c;
  let failed = false;

  for (let cursor = -1; cursor++, c = input[cursor]; cursor < input.length) {
    if (/[A-Za-z]/.test(c)) {
      scratchpad += c;
    }
    else {
      if (scratchpad.length != 0) {
        tokens.push({ type: 'V', value: scratchpad })
        scratchpad = "";
      }

      if (c == ' ') {} // Skip whitespaces
      else if (c == '(' || c == ')') {
        tokens.push({ type: c })
      }
      else if (Object.values(Connective).includes(c)) {
        tokens.push({ type: c })
      }
      else {
        failed = true;
        break;
      }
    }
  }

  if (failed) {
    return null;
  }

  if (scratchpad.length != 0) {
    tokens.push({ type: 'V', value: scratchpad })
    scratchpad = "";
  }

  return tokens;
}

function parse_input_field() {
  let input = input_panel_field.value;
  let tokens = tokenize(input);
  let pos = 0;

  if (tokens === null) {
    input_panel_error.innerHTML = "Tokenizer error: stop using silly characters";
    return null;
  }

  let peek = () => tokens[pos];
  let consume = (type) => {
    let next = peek();
    if (next && next.type === type) {
      return tokens[pos++];
    } else {
      return null;
    }
  }

  // Grammar:
  // form    := iff
  // iff     := impl (↔ iff)*
  // impl    := or (→ impl)*
  // or      := and (∨ or)*
  // and     := unary (∧ and)*
  // unary   := ¬ unary | atom
  // primary := ⊥ | forall VAR . expr | exists VAR . expr
  //          | "(" expr ")"; if fails, term_expr
  //
  // rel   := term_add = term_add | term_add < term_add
  // term  := term_add
  // add  := mul (+ add)*
  // mul  := succ (x mul)*
  // succ := ↑ succ | atom
  // atom := 0 | VAR | "(" term ")"

  let parse_form = () => {
    return parse_iff();
  }

  let parse_binary = (next_call, connective, expression_constructor) => {
    let res = next_call();
    if (!res) {
      return null;
    }

    while (consume(connective)) {
      let arg2 = parse_binary(next_call, connective, expression_constructor);
      // Note the recursion: A ∧ B ∧ C is valid and is parsed as A ∧ (B ∧ C)
      if (!arg2) {
        return null;
      }
      res = expression_constructor(res, arg2);
      next_token = tokens[pos];
    }
    return res;
  }

  function parse_iff () { return parse_binary(parse_impl , Connective.IFF , Expression.EIff ); }
  function parse_impl() { return parse_binary(parse_or   , Connective.IMPL, Expression.EImpl); }
  function parse_or  () { return parse_binary(parse_and  , Connective.OR  , Expression.EOr  ); }
  function parse_and () { return parse_binary(parse_unary, Connective.AND , Expression.EAnd ); }

  function parse_unary() {
    let next_token = tokens[pos];
    if (!next_token) {
      return null;
    } else if (next_token.type === Connective.NOT) {
      pos++;
      let arg = parse_unary();
      if (!arg) {
        return null;
      }
      return Expression.ENot(arg); // Implicit negation nesting is supported
    }
    return parse_primary();
  }

  function parse_primary() {
    let next_token = tokens[pos];
    if (!next_token) {
      return null;
    }

    if (next_token.type === Connective.FALSE) {
      pos++;
      return Expression.EFalse();
    } else if (next_token.type === '(') {
      pos++;
      const e = parse_form();
      if (!e || !consume(')')) {
        return null;
      }
      return e;
    } else if (next_token.type === Connective.FORALL || next_token.type === Connective.EXISTS) {
      const quantifier = next_token.type;
      pos++;
      next_token = tokens[pos];
      if (!next_token || next_token.type !== 'V') {
        return null;
      }
      const bound_var = next_token.value;
      pos++;
      if (!consume(Connective.DOT)) {
        return null;
      }
      const e = parse_form();
      if (!e) {
        return null;
      }
      if (quantifier === Connective.FORALL) {
        return Expression.EForall(bound_var, e);
      } else {
        return Expression.EExists(bound_var, e);
      }
    } else {
      return parse_rel();
    }
  }

  function parse_rel() {
    const t1 = parse_add();
    if (!t1) {
      return null;
    }

    if (consume("=")) {
      const t2 = parse_add();
      return Expression.TEq(t1, t2);
    } else if (consume("<")) {
      const t2 = parse_add();
      return Expression.TLt(t1, t2);
    }
    return t1;
  }

  function parse_add() { return parse_binary(parse_mul , Connective.ADD, Expression.TAdd); }
  function parse_mul() { return parse_binary(parse_succ, Connective.MUL, Expression.TMul); }

  function parse_succ() {
    if (consume(Connective.SUCC)) {
      const t = parse_succ();
      if (!t) { return null; }
      return Expression.TSucc(t);
    } else {
      return parse_atom();
    }
  }

  function parse_atom() {
    if (consume(Connective.ZERO)) {
      return Expression.TZero();
    } else if (consume('(')) {
      let t = parse_add();
      if (!t) { return null; }
      if (!consume(')')) { return null; }
      return t;
    } else if (tokens[pos] && tokens[pos].type == 'V') {
      ++pos;
      return Expression.TVar(tokens[pos - 1].value);
    }
    return null;
  }

  let tree = parse_form(tokens);
  if (tree == null) {
    input_panel_error.innerHTML = "Parser error: show more respect to the grammar";
    return null;
  }
  return tree;
}


// Expression input: input panel management
var is_input_panel_open = false; // Yay, more global state
function open_input_panel(title, callback) {
  input_panel_title.innerHTML = title;
  input_panel_error.innerHTML = " ";
  input_panel_confirm.onclick = function() { callback() };
  is_input_panel_open = true;
  input_panel.style.display = "block";
  document.documentElement.style.overflow = "hidden";
  document.body.scroll = "no";
  input_panel_field.value = "";
  input_panel_field.focus();
}

function insert_special_symbol(symbol) { // Called from the special symbol buttoms
  input_panel_field.setRangeText(symbol.textContent);
  input_panel_field.selectionEnd += 1;
  input_panel_field.selectionStart = input_panel_field.selectionEnd;
}

function close_input_panel_click_handler(event, element) {
  if (event.target == element) {
    close_input_panel();
  } else {
    event.stopPropagation();
  }
}

function close_input_panel() {
  is_input_panel_open = false;
  input_panel.style.display = "none";
  document.documentElement.style.overflow = "scroll";
  document.body.scroll = "yes";
}


// Level/input panel: escape to exit and other input niceties
document.onkeydown = function(evt) {
  if (is_input_panel_open && "key" in evt) {
    if (evt.key === "Escape" || evt.key === "Esc") {
      close_input_panel();
    }
    else if (evt.key === "Enter") {
      input_panel_confirm.onclick();
    }
  }
  else if (is_level_panel_open && "key" in evt) {
    if (evt.key === "Escape" || evt.key === "Esc") {
      close_level_panel();
    }
  }
  else if (is_help_panel_open && "key" in evt) {
    if (evt.key === "Escape" || evt.key === "Esc") {
      close_help_panel();
    }
  }
}


// Rules
// Note: we do not draw separators and the tree as neatly as we could. Right now, a separator is
// always as wide as all the subtrees sitting above it, which is not how it is done in Van Dalen.
function set_separator(name) {
  let sep = focus.parentNode.parentNode.children[1];
  sep.innerHTML = `<div class=sep-bar></div><div class=sep-name>${name}</div>`;
}

function apply_axiom_rule(name) {
  clear_above(focus);
  set_separator(name);
  focus.classList.add("known");
  update_status_of_lower_tree(focus);
  update_contextual_actions();
  check_whether_proof_done();
}

function apply_rule(name, rule_function, arg = null) {
  clear_above(focus);
  let expr = JSON.parse(focus.getAttribute("data-expr"));
  let result = rule_function(expr, arg);
  if (result === false) { return; } // Rule rejected (e.g. side condition failed)
  set_separator(name);
  update_status_of_lower_tree(focus);
  set_focus(focus.parentNode.parentNode.children[0].children[0].children[2].children[0]);
  check_whether_proof_done();
}

function apply_rule_with_arg_callback(name, input_callback, additional_verif = null) {
  let parse_res = parse_input_field();
  if (parse_res === null) {
    return;
  }
  if (additional_verif) {
    if (!additional_verif(parse_res)) {
      return;
    }
  }
  close_input_panel();
  apply_rule(name, input_callback, parse_res);
}

function apply_rule_with_arg(name, arg_input_string, input_callback, additional_verif = null) {
  open_input_panel(arg_input_string, () => apply_rule_with_arg_callback(name, input_callback, additional_verif));
}

function validate_or_input(parse_res) {
  switch (parse_res.type) {
    case "Or": return true;
    default  : input_panel_error.innerHTML = "Type error: Or-expression expected"; return false;
  }
}



function validate_eq_input(parse_res) {
  if (parse_res.type === "Eq") {
    return true;
  }
  input_panel_error.innerHTML = "Type error: expected an equality (e.g. x = y)";
  return false;
}

function is_known(expr, node) {
  let parsed = JSON.parse(expr);
  for (let i = 0; i < premises_holder.children.length; i++) {
    let p = premises_holder.children[i];
    if (expr_equal(parsed, JSON.parse(p.getAttribute("data-expr")))) {
      return p;
    }
  }

  return null;
}

function update_known(node) {
  let known_cause = is_known(node.getAttribute("data-expr"), node);
  if (known_cause) {
    node.known = known_cause;
    node.classList.add("known");
    update_status_of_lower_tree(node);
  } else if (!node.parentNode.parentNode.children[1].innerHTML) {
    // Only un-mark leaf nodes (no rule applied above)
    node.known = null;
    node.classList.remove("known");
  }
}

function add_hyp(tree) {
  // Would be less ugly with raw HTML embedded
  let new_hyp = document.createElement("div");
  new_hyp.className = "subtree";
  let new_hyp_sep = document.createElement("div");
  new_hyp_sep.className = "sep";
  let new_hyp_hyps = document.createElement("div");
  new_hyp_hyps.className = "hyps";
  let new_hyp_concl = document.createElement("div");
  new_hyp_concl.className = "concl";
  let hyp_expr = document.createElement("div");
  hyp_expr.innerHTML = tree_to_html(tree);
  hyp_expr.className = "expr pseudo-button";
  hyp_expr.onclick = function() { set_focus(this); };
  data_expr = JSON.stringify(tree);
  hyp_expr.setAttribute("data-expr", data_expr);
  new_hyp_concl.appendChild(hyp_expr);
  new_hyp.appendChild(new_hyp_hyps);
  new_hyp.appendChild(new_hyp_sep);
  new_hyp.appendChild(new_hyp_concl);
  focus.parentNode.parentNode.querySelector(".hyps").appendChild(new_hyp);
  let known = is_known(data_expr, focus);
  if (known) {
    hyp_expr.classList.add("known");
    hyp_expr.known = known;
  }
  return new_hyp;
}

// Recheck known status of whole proof tree (e.g. after premise changes)
function recheck_status_of_tree(tree) {
  if (tree.known) {
    tree.known.removeAttribute("id");
  }
  set_focus(tree);

  // Check if this node has proof work above (non-empty separator)
  let sep = tree.parentNode.parentNode.children[1];
  let has_proof_above = sep && sep.innerHTML !== "";

  if (has_proof_above) {
    // Node has a rule applied — check if all children above are known
    let subtrees = tree.parentNode.parentNode.children[0].children;
    let success_for_all = true;
    for (let t of subtrees) {
      if (!recheck_status_of_tree(t.children[2].children[0])) {
        success_for_all = false;
      }
    }
    if (success_for_all) {
      tree.classList.add("known");
    } else {
      tree.classList.remove("known");
    }
    tree.known = null;
    return success_for_all;
  }

  // Leaf node — check if it matches a premise
  let known = is_known(tree.getAttribute("data-expr"), tree);
  if (known) {
    tree.known = known;
    tree.classList.add("known");
    return true;
  } else {
    tree.known = null;
    tree.classList.remove("known");
    return false;
  }
}

// Structural equality check for expressions/terms
function expr_equal(a, b) {
  function go(a, b, env) {
    if (a.type !== b.type) return false;
    switch (a.type) {
      case "False": case "Zero": return true;
      case "Var":
        let ma = env.get(a.name), mb = env.get(b.name);
        if (ma !== undefined || mb !== undefined) return ma === b.name && mb === a.name;
        return a.name === b.name;
      case "Not":    return go(a.e, b.e, env);
      case "Succ":   return go(a.t, b.t, env);
      case "And": case "Or": case "Impl": case "Iff":
        return go(a.e1, b.e1, env) && go(a.e2, b.e2, env);
      case "Eq": case "Lt": case "Add": case "Mul":
        return go(a.t1, b.t1, env) && go(a.t2, b.t2, env);
      case "Forall": case "Exists":
        let env2 = new Map(env);
        env2.set(a.bound_var, b.bound_var);
        env2.set(b.bound_var, a.bound_var);
        return go(a.e, b.e, env2);
      default: return false;
    }
  }
  return go(a, b, new Map());
}

// Replace all occurrences of `old_term` with `new_term` in `expr` (structural)
function term_replace(expr, old_term, new_term) {
  if (expr_equal(expr, old_term)) return new_term;
  switch (expr.type) {
    case "False": case "Zero": case "Var": return expr;
    case "Not":   return { type: "Not", e: term_replace(expr.e, old_term, new_term) };
    case "Succ":  return { type: "Succ", t: term_replace(expr.t, old_term, new_term) };
    case "And":   return { type: "And",  e1: term_replace(expr.e1, old_term, new_term), e2: term_replace(expr.e2, old_term, new_term) };
    case "Or":    return { type: "Or",   e1: term_replace(expr.e1, old_term, new_term), e2: term_replace(expr.e2, old_term, new_term) };
    case "Impl":  return { type: "Impl", e1: term_replace(expr.e1, old_term, new_term), e2: term_replace(expr.e2, old_term, new_term) };
    case "Iff":   return { type: "Iff",  e1: term_replace(expr.e1, old_term, new_term), e2: term_replace(expr.e2, old_term, new_term) };
    case "Eq":    return { type: "Eq",   t1: term_replace(expr.t1, old_term, new_term), t2: term_replace(expr.t2, old_term, new_term) };
    case "Lt":    return { type: "Lt",   t1: term_replace(expr.t1, old_term, new_term), t2: term_replace(expr.t2, old_term, new_term) };
    case "Add":   return { type: "Add",  t1: term_replace(expr.t1, old_term, new_term), t2: term_replace(expr.t2, old_term, new_term) };
    case "Mul":   return { type: "Mul",  t1: term_replace(expr.t1, old_term, new_term), t2: term_replace(expr.t2, old_term, new_term) };
    case "Forall": case "Exists": {
      let fv_old = free_vars(old_term), fv_new = free_vars(new_term);
      // Bound var shadows old_term — can't match inside
      if (fv_old.has(expr.bound_var)) return expr;
      // Bound var would capture a free var in new_term — alpha-rename first
      let e = expr;
      if (fv_new.has(e.bound_var)) {
        let avoid = new Set([...fv_old, ...fv_new, ...free_vars(e.e)]);
        let fresh = fresh_var(avoid);
        e = { type: e.type, bound_var: fresh, e: substitute(e.e, e.bound_var, { type: "Var", name: fresh }) };
      }
      return { type: e.type, bound_var: e.bound_var, e: term_replace(e.e, old_term, new_term) };
    }
    default: return expr;
  }
}

// Substitute free occurrences of `name` with `term` in `expr`
function substitute(expr, name, term) {
  switch (expr.type) {
    case "False": return expr;
    case "Var":   return expr.name === name ? term : expr;
    case "Not":   return { type: "Not", e: substitute(expr.e, name, term) };
    case "And":   return { type: "And", e1: substitute(expr.e1, name, term), e2: substitute(expr.e2, name, term) };
    case "Or":    return { type: "Or",  e1: substitute(expr.e1, name, term), e2: substitute(expr.e2, name, term) };
    case "Impl":  return { type: "Impl", e1: substitute(expr.e1, name, term), e2: substitute(expr.e2, name, term) };
    case "Iff":   return { type: "Iff", e1: substitute(expr.e1, name, term), e2: substitute(expr.e2, name, term) };
    case "Forall": case "Exists": {
      if (expr.bound_var === name) return expr; // shadowed
      // Bound var would capture a free var in term — alpha-rename first
      let e = expr;
      if (free_vars(term).has(e.bound_var)) {
        let avoid = new Set([...free_vars(term), ...free_vars(e.e), name]);
        let fresh = fresh_var(avoid);
        e = { type: e.type, bound_var: fresh, e: substitute(e.e, e.bound_var, { type: "Var", name: fresh }) };
      }
      return { type: e.type, bound_var: e.bound_var, e: substitute(e.e, name, term) };
    }
    case "Eq":    return { type: "Eq",  t1: substitute(expr.t1, name, term), t2: substitute(expr.t2, name, term) };
    case "Lt":    return { type: "Lt",  t1: substitute(expr.t1, name, term), t2: substitute(expr.t2, name, term) };
    case "Add":   return { type: "Add", t1: substitute(expr.t1, name, term), t2: substitute(expr.t2, name, term) };
    case "Mul":   return { type: "Mul", t1: substitute(expr.t1, name, term), t2: substitute(expr.t2, name, term) };
    case "Succ":  return { type: "Succ", t: substitute(expr.t, name, term) };
    case "Zero":  return expr;
    default: return expr;
  }
}

function impl_intro(expr) { add_hyp(expr.e2); }
function or_intro_l(expr) { add_hyp(expr.e1); }
function or_intro_r(expr) { add_hyp(expr.e2); }
function and_intro(expr) { add_hyp(expr.e1); add_hyp(expr.e2); }
function iff_intro(expr) {
  add_hyp({"type": "Impl", "e1": expr.e1, "e2": expr.e2});
  add_hyp({"type": "Impl", "e1": expr.e2, "e2": expr.e1});
}
function not_intro(expr) { add_hyp({"type": "Impl", "e1": expr.e, "e2": {"type": "False"}}); }
// ∃-intro: goal is ∃x.P(x), user provides witness t, hypothesis is P(t/x)
// Collect free variables in an expression
function free_vars(expr) {
  switch (expr.type) {
    case "False": case "Zero": return new Set();
    case "Var":    return new Set([expr.name]);
    case "Not":    return free_vars(expr.e);
    case "Succ":   return free_vars(expr.t);
    case "And": case "Or": case "Impl": case "Iff":
      return new Set([...free_vars(expr.e1), ...free_vars(expr.e2)]);
    case "Eq": case "Lt": case "Add": case "Mul":
      return new Set([...free_vars(expr.t1), ...free_vars(expr.t2)]);
    case "Forall": case "Exists": {
      let fv = free_vars(expr.e);
      fv.delete(expr.bound_var);
      return fv;
    }
    default: return new Set();
  }
}

function fresh_var(avoid) {
  let names = "abcdefghijklmnopqrstuvwxyz";
  for (let round = 0; ; round++) {
    let suffix = round === 0 ? "" : String(round);
    for (let c of names) {
      let candidate = c + suffix;
      if (!avoid.has(candidate)) return candidate;
    }
  }
}

function flash_rule_error(msg) {
  done_message.style.visibility = "visible";
  done_message.style.color = "var(--red)";
  done_message.textContent = msg;
  setTimeout(() => {
    done_message.style.color = "var(--green)";
    done_message.textContent = "Branch done";
    done_message.style.visibility = "hidden";
    // Restore if the branch is actually done
    if (focus.classList.contains("known")) {
      done_message.style.visibility = "visible";
    }
  }, 2000);
}

// ∃-elim: user provides ∃x.P(x), adds ∃x.P(x) and ∀x.(P(x) → C) as hypotheses
function exists_elim(expr, arg) {
  let v = arg.bound_var;
  if (free_vars(expr).has(v)) {
    flash_rule_error(`∃-elim: "${v}" is free in the goal`);
    return false;
  }
  for (let i = 0; i < premises_holder.children.length; i++) {
    let p = JSON.parse(premises_holder.children[i].getAttribute("data-expr"));
    if (free_vars(p).has(v)) {
      flash_rule_error(`∃-elim: "${v}" is free in a premise`);
      return false;
    }
  }
  add_hyp(arg);
  add_hyp({ type: "Forall", bound_var: v, e: { type: "Impl", e1: arg.e, e2: expr } });
}
function exists_elim_validate(parse_res) {
  if (parse_res.type === "Exists") return true;
  input_panel_error.innerHTML = "Type error: expected ∃x.P(x)";
  return false;
}
// Check if target is an instance of pattern[var_name := ?] for some term
function is_instance_of(pattern, target, var_name) {
  let binding = undefined;
  function go(p, t) {
    if (p.type === "Var" && p.name === var_name) {
      if (binding === undefined) { binding = t; return true; }
      return expr_equal(binding, t);
    }
    if (p.type !== t.type) return false;
    switch (p.type) {
      case "False": case "Zero": return true;
      case "Var":  return p.name === t.name;
      case "Not":  return go(p.e, t.e);
      case "Succ": return go(p.t, t.t);
      case "And": case "Or": case "Impl": case "Iff":
        return go(p.e1, t.e1) && go(p.e2, t.e2);
      case "Eq": case "Lt": case "Add": case "Mul":
        return go(p.t1, t.t1) && go(p.t2, t.t2);
      case "Forall": case "Exists":
        if (p.bound_var === var_name) return expr_equal(p, t);
        if (p.bound_var !== t.bound_var) return false;
        return go(p.e, t.e);
      default: return false;
    }
  }
  return go(pattern, target);
}
// ∀-elim: user provides ∀x.P(x), goal must be an instance of P
function forall_elim(expr, arg) {
  if (!is_instance_of(arg.e, expr, arg.bound_var)) {
    flash_rule_error(`∀-elim: goal is not an instance of the body`);
    return false;
  }
  add_hyp(arg);
}
function forall_elim_validate(parse_res) {
  if (parse_res.type === "Forall") return true;
  input_panel_error.innerHTML = "Type error: expected ∀x.P(x)";
  return false;
}
// ∀-intro: goal is ∀x.P(x), hypothesis is P(x)
// Side condition: bound_var must not be free in any current premise
function forall_intro(expr, skip_check) {
  if (!skip_check) {
    let v = expr.bound_var;
    for (let i = 0; i < premises_holder.children.length; i++) {
      let p = JSON.parse(premises_holder.children[i].getAttribute("data-expr"));
      if (free_vars(p).has(v)) {
        flash_rule_error(`∀-intro: "${v}" is free in a premise`);
        return false;
      }
    }
  }
  add_hyp(expr.e);
}
function exists_intro(expr, arg) {
  add_hyp(substitute(expr.e, expr.bound_var, arg));
}
// For rebuild: arg is the pre-computed hypothesis P(t/x)
function exists_intro_rebuild(expr, arg) {
  add_hyp(arg);
}
function and_elim_l(expr, arg) { add_hyp({"type": "And", "e1": expr, "e2": arg}); }
function and_elim_r(expr, arg) { add_hyp({"type": "And", "e1": arg, "e2": expr}); }
function or_elim(expr, arg) {
  add_hyp(arg);
  add_hyp({"type": "Impl", "e1": arg.e1, "e2": expr});
  add_hyp({"type": "Impl", "e1": arg.e2, "e2": expr});
}
function iff_elim_l(expr, arg) {
  add_hyp({"type": "Iff", "e1": expr, "e2": arg});
  add_hyp(arg);
}
function iff_elim_r(expr, arg) {
  add_hyp({"type": "Iff", "e1": arg, "e2": expr});
  add_hyp(arg);
}
function false_elim() { add_hyp({"type": "False"}); }
function impl_elim(expr, arg) {
  add_hyp(arg);
  add_hyp({"type": "Impl", "e1": arg, "e2": expr});
}
function dne(expr) {
  add_hyp({"type": "Not", "e": {"type": "Not", "e": expr}});
}
function not_elim(expr, arg) {
  add_hyp(arg);
  add_hyp({"type": "Not", "e": arg});
}
// add-zero: a + 0 = c → a = c, or c = a + 0 → c = a
function add_zero_rule(expr) {
  if (expr.t1.type === "Add" && expr.t1.t2.type === "Zero") {
    add_hyp({ type: "Eq", t1: expr.t1.t1, t2: expr.t2 });
  } else {
    add_hyp({ type: "Eq", t1: expr.t1, t2: expr.t2.t1 });
  }
}
// add-succ: a + ↑b = c → ↑(a + b) = c, or c = a + ↑b → c = ↑(a + b)
function add_succ_rule(expr) {
  let rewritten = function(side) {
    return { type: "Succ", t: { type: "Add", t1: side.t1, t2: side.t2.t } };
  };
  if (expr.t1.type === "Add" && expr.t1.t2.type === "Succ") {
    add_hyp({ type: "Eq", t1: rewritten(expr.t1), t2: expr.t2 });
  } else {
    add_hyp({ type: "Eq", t1: expr.t1, t2: rewritten(expr.t2) });
  }
}
// succ-inj: goal is a = b, subgoal is ↑a = ↑b
function succ_inj_rule(expr) {
  add_hyp({ type: "Eq", t1: { type: "Succ", t: expr.t1 }, t2: { type: "Succ", t: expr.t2 } });
}
// succ-cancel: goal is ↑a = ↑b, subgoal is a = b
function succ_cancel_rule(expr) {
  add_hyp({ type: "Eq", t1: expr.t1.t, t2: expr.t2.t });
}
// mul-zero: a * 0 = c → 0 = c, or c = a * 0 → c = 0
function mul_zero_rule(expr) {
  if (expr.t1.type === "Mul" && expr.t1.t2.type === "Zero") {
    add_hyp({ type: "Eq", t1: { type: "Zero" }, t2: expr.t2 });
  } else {
    add_hyp({ type: "Eq", t1: expr.t1, t2: { type: "Zero" } });
  }
}
// mul-succ: a * ↑b = c → (a * b) + a = c, or c = a * ↑b → c = (a * b) + a
function mul_succ_rule(expr) {
  let rewritten = function(side) {
    return { type: "Add", t1: { type: "Mul", t1: side.t1, t2: side.t2.t }, t2: side.t1 };
  };
  if (expr.t1.type === "Mul" && expr.t1.t2.type === "Succ") {
    add_hyp({ type: "Eq", t1: rewritten(expr.t1), t2: expr.t2 });
  } else {
    add_hyp({ type: "Eq", t1: expr.t1, t2: rewritten(expr.t2) });
  }
}
// =-elim: user provides equality t1 = t2; hypotheses are t1 = t2 and goal[t2 := t1]
function eq_elim(expr, arg) {
  add_hyp(arg);
  add_hyp(term_replace(expr, arg.t2, arg.t1));
}
// Induction on ∀x.P(x): base case P(0), step ∀x.(P(x) → P(↑x))
function peano_induction(expr) {
  let v = expr.bound_var;
  let body = expr.e;
  let p_zero = substitute(body, v, { type: "Zero" });
  let p_succ = substitute(body, v, { type: "Succ", t: { type: "Var", name: v } });
  add_hyp(p_zero);
  add_hyp({ type: "Forall", bound_var: v, e: { type: "Impl", e1: body, e2: p_succ } });
}


// Premises management
function recheck_status_of_whole_tree() { // Inserting/removing premises can change everything
  let og_focus = focus;
  recheck_status_of_tree(proof.children[0].children[2].children[0]);
  check_whether_proof_done();
  update_contextual_actions();
  if (og_focus.parentNode) {
    set_focus(og_focus);
  }
}

function append_premise(premise, global = false) {
  if (!global) {
    var cross = document.createElement("div");
    cross.className = "remove-cross pseudo-button";
    cross.setAttribute("onclick", "remove_premise(this)");
    cross.innerHTML = "x";
    premise.appendChild(cross);
  }
  premises_holder.appendChild(premise);
  if (global) {
    recheck_status_of_whole_tree();
  }
}

function insert_premise(premise, global = false, cause = undefined) {
  var new_premise = document.createElement("div");
  new_premise.classList.add("expr");
  if (global) {
    new_premise.classList.add("global-premise")
  } else {
    new_premise.cause = cause;
    new_premise.onmouseenter = function () {
      this.cause.classList.add("known-cause-for-premise");
    }
    new_premise.onmouseleave = function () {
      this.cause.classList.remove("known-cause-for-premise");
    };
  }
  new_premise.setAttribute("data-expr", JSON.stringify(premise));
  new_premise.innerHTML = tree_to_html(premise);
  append_premise(new_premise, global);
}

function confirm_input_premise() {
  let parse_res = parse_input_field();
  if (parse_res === null) {
    return;
  }
  close_input_panel();
  insert_premise(parse_res);
}

function add_premise() {
  open_input_panel("New premise:", confirm_input_premise);
}

function remove_premise(premise) {
  premise.parentNode.remove();
  recheck_status_of_whole_tree();
}


// Local premises management
// We don't do anything smart for the common case of just moving one step down a branch.
function clear_old_premises() {
  let to_remove = [];
  for (let i = 0; i < premises_holder.children.length; i++) {
    let p = premises_holder.children[i];
    if (!p.classList.contains("global-premise")) {
      to_remove.push(p);
    }
  }
  for (p of to_remove) {
    p.remove();
  }
}

function insert_local_premises() {
  // TODO maintain a more logical order in the list of premises: more local ones should appear
  // closer to the end.
  let to_add = []; // This is a cheap way of getting them at least somewhat in order

  // From impl
  let p = focus.parentNode.parentNode.parentNode.parentNode.children[2];
  while (p && p.className === "concl") {
    const attr = JSON.parse(p.children[0].getAttribute("data-expr"));
    const sep_name = p.parentNode.children[1].children[1];
    if (sep_name && sep_name.innerHTML == "→-intro" && attr.type === "Impl") {
      to_add.push([attr.e1, false, p.children[0]]);
    }
    p = p.parentNode.parentNode.parentNode.children[2];
  }

  // From RAA
  p = focus.parentNode;
  while (p && p.className === "concl") {
    const attr = JSON.parse(p.children[0].getAttribute("data-expr"));
    if (attr.type === "False") {
      const below = p.parentNode.parentNode.parentNode.children[2];
      const sep_name = p.parentNode.parentNode.parentNode.children[1].children[1];
      if (sep_name && sep_name.innerHTML == "⊥-elim") {
        if (below && below.classList.contains("concl")) {
          const below_attr = JSON.parse(below.children[0].getAttribute("data-expr"));
          to_add.push([{"type": "Not", "e": below_attr}, false, below.children[0]]);
        }
      }
    }
    p = p.parentNode.parentNode.parentNode.children[2];
  }

  for (i = to_add.length - 1; i >= 0; --i) {
    const x = to_add[i];
    insert_premise(x[0], x[1], x[2]);
  }
}

function update_premises() {
  clear_old_premises();
  insert_local_premises();
}


// Special actions
function clear_above(x) {
  x.parentNode.parentNode.querySelector(".hyps").innerHTML = "";
  x.parentNode.parentNode.querySelector(".sep").innerHTML = "";
  x.classList.remove("known");
}

function apply_clear_above() {
  clear_above(focus);
  recheck_status_of_whole_tree();
}

function apply_as_premise() {
  let clone = focus.cloneNode(true);
  clone.id = "";
  clone.onclick = "";
  clone.className = "expr";
  append_premise(clone);
}

function confirm_change() {
  let parse_res = parse_input_field();
  if (parse_res === null) {
    return;
  }
  close_input_panel();
  focus.innerHTML = tree_to_html(parse_res);
  focus.setAttribute("data-expr", JSON.stringify(parse_res));
  clear_above(focus);
  update_contextual_actions();
  check_whether_proof_done();
}
function apply_change() {
  open_input_panel("New value for node:", confirm_change);
}

function reset_current_exercise() {
  set_focus(proof.children[0].children[2].children[0]);
  apply_clear_above();
}


// Refresh context
function update_contextual_actions() {
  let impl_intro  = `<div class="rule pseudo-button" onclick='apply_rule("→-intro", impl_intro)'>→-intro</div>`;
  let iff_intro   = `<div class="rule pseudo-button" onclick='apply_rule("↔-intro", iff_intro)'>↔-intro</div>`;
  let and_intro   = `<div class="rule pseudo-button" onclick='apply_rule("∧-intro", and_intro)'>∧-intro</div>`;
  let or_intro_l  = `<div class="rule pseudo-button" onclick='apply_rule("∨-intro-l", or_intro_l)'>∨-intro-l</div>`;
  let or_intro_r  = `<div class="rule pseudo-button" onclick='apply_rule("∨-intro-r", or_intro_r)'>∨-intro-r</div>`;
  let not_intro   = `<div class="rule pseudo-button" onclick='apply_rule("¬-intro", not_intro, "Hypothesis:")'>¬-intro</div>`;
  let not_elim    = `<div class="rule pseudo-button" onclick='apply_rule_with_arg("¬-elim", "Hypothesis:", not_elim)'>¬-elim</div>`;
  let forall_intro = `<div class="rule pseudo-button" onclick='apply_rule("∀-intro", forall_intro)'>∀-intro</div>`;
  let exists_intro = `<div class="rule pseudo-button" onclick='apply_rule_with_arg("∃-intro", "Witness term:", exists_intro)'>∃-intro</div>`;

  if (focus.classList.contains("known")) {
    intro_rules.style.visibility = "hidden";
    elim_rules.style.visibility = "hidden";
    special_rules.style.visibility = "hidden";
    done_message.style.visibility = "visible";
  } else {
    intro_rules.style.visibility = "visible";
    elim_rules.style.visibility = "visible";
    special_rules.style.visibility = "visible";
    done_message.style.visibility = "hidden";
  }

  let expr = JSON.parse(focus.getAttribute("data-expr"));
  let rules = "";

  // Standard intro rules based on top-level type
  switch (expr.type) {
    case "False": rules += not_elim; break;
    case "Not"  : rules += not_intro; break;
    case "And"  : rules += and_intro; break;
    case "Or"   : rules += or_intro_l + or_intro_r; break;
    case "Impl" : rules += impl_intro; break;
    case "Iff"  : rules += iff_intro; break;
    case "Forall": rules += forall_intro + `<div class="rule pseudo-button" onclick='apply_rule("induction", peano_induction)'>induction</div>`; break;
    case "Exists": rules += exists_intro; break;
  }

  // Axiom rules: shown when the focused node matches the pattern
  if (matches_eq_intro(expr))       rules += `<div class="rule pseudo-button" onclick='apply_axiom_rule("=-intro")'>=-intro</div>`;
  if (matches_add_zero(expr))       rules += `<div class="rule pseudo-button" onclick='apply_rule("add-zero", add_zero_rule)'>add-zero</div>`;
  if (matches_add_succ(expr))       rules += `<div class="rule pseudo-button" onclick='apply_rule("add-succ", add_succ_rule)'>add-succ</div>`;
  if (matches_succ_cancel(expr))   rules += `<div class="rule pseudo-button" onclick='apply_rule("succ-cancel", succ_cancel_rule)'>succ-cancel</div>`;
  if (matches_mul_zero(expr))       rules += `<div class="rule pseudo-button" onclick='apply_rule("mul-zero", mul_zero_rule)'>mul-zero</div>`;
  if (matches_mul_succ(expr))       rules += `<div class="rule pseudo-button" onclick='apply_rule("mul-succ", mul_succ_rule)'>mul-succ</div>`;
  if (matches_succ_inj(expr))       rules += `<div class="rule pseudo-button" onclick='apply_rule("succ-inj", succ_inj_rule)'>succ-inj</div>`;
  if (matches_zero_neq_succ(expr))  rules += `<div class="rule pseudo-button" onclick='apply_axiom_rule("zero≠succ")'>zero≠succ</div>`;
  if (matches_lt_zero(expr))        rules += `<div class="rule pseudo-button" onclick='apply_axiom_rule("lt-zero")'>lt-zero</div>`;
  if (matches_lt_succ(expr))        rules += `<div class="rule pseudo-button" onclick='apply_axiom_rule("lt-succ")'>lt-succ</div>`;

  intro_rules_holder.innerHTML = rules;

  if (proof.children[0].children[2].children[0] === focus) {
    change_button.style.visibility = "visible";
  } else {
    change_button.style.visibility = "hidden";
  }
}


// TODO follow cursor
// Zooming, drag around
let scale = 1;
proof_top.style.transformOrigin = "center center";
drag_box.addEventListener("wheel", (e) => {
  if (!e.ctrlKey) return;
  e.preventDefault();

  const rect = drag_box.getBoundingClientRect();
  const offsetX = e.clientX - rect.left;
  const offsetY = e.clientY - rect.top;

  const og_scale = scale;
  scale += e.deltaY < 0 ? 0.1 : -0.1;
  scale = Math.min(Math.max(scale, 0.5), 3);
  const scale_ratio = scale/og_scale;

  proof_top.style.transform = `scale(${scale})`;

  drag_box.scrollLeft = (drag_box.scrollLeft + offsetX) * scale_ratio - offsetX;
  drag_box.scrollTop  = (drag_box.scrollTop  + offsetY) * scale_ratio - offsetY;
}, { passive: false });

// From https://stackoverflow.com/a/66313884
let mouseDown = false;
let startX, startY, scrollLeft, scrollTop;
const slider = drag_box;

const startDragging = (e) => {
  mouseDown = true;
  startX = e.pageX - slider.offsetLeft;
  startY = e.pageY - slider.offsetTop;
  scrollLeft = slider.scrollLeft;
  scrollTop = slider.scrollTop;
}

const stopDragging = (e) => {
  mouseDown = false;
}

const move = (e) => {
  e.preventDefault();
  if (!mouseDown) { return; }
  const x = e.pageX - slider.offsetLeft;
  const scrollX = x - startX;
  slider.scrollLeft = scrollLeft - scrollX;
  const y = e.pageY - slider.offsetTop;
  const scrollY = y - startY;
  slider.scrollTop = scrollTop - scrollY;
}

slider.addEventListener("mousemove", move, false);
slider.addEventListener("mousedown", startDragging, false);
slider.addEventListener("mouseup", stopDragging, false);
slider.addEventListener("mouseleave", stopDragging, false);


// Themes
function invert_lightness() {
  const root = document.querySelector(':root');
  const css_variables = [
    "--black"  , "--level-a", "--level-b", "--level-c", "--white" , "--ghost",
  ];

  function invert_255(x) { return 255 - x; }
  function invert_100(x) { return 100 - x; }

  function get_hue(s) {
    s = s.substring(s.indexOf("(") + 1);
    return s.split(" ")[0];
  }
  function get_saturation(s) {
    s = s.split("%")[0];
    s = s.split(" ");
    return s[s.length - 1]
  }
  function get_lightness(s) {
    s = s.split("%")[1];
    s = s.split(" ");
    return s[s.length - 1]
  }

  function to_color_string(h, s, l) {
    return "hsl(" + h + " " + s + "% " + l + "%)";
  }

  let rc = getComputedStyle(root);
  for (v of css_variables) {
    let v_string = rc.getPropertyValue(v);
    let h = invert_255(get_hue(v_string));
    let s = get_saturation(v_string);
    let l = invert_100(get_lightness(v_string));
    root.style.setProperty(v, to_color_string(h, s, l));
  }
}


// Initialization
function init() {
  populate_level_selector();
  persistent_load();
  load_current_level(); // current_exercise is set by persistent load
}
init();
