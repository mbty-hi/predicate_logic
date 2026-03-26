// I hope you like spaghetti code

// This code is a bit of a mess, at least in a small part due to the fact that we switch between
// four distinct representations for expressions:
// * Raw strings (for input only)
// * An inductive representation (or the poor man's version thereof, courtesy of JS)
// * The same sort-of inductive representation serialized as a string
// * The HTML representation (the node you actually see)
// HTML nodes actually store the serialized inductive representation of their contents via their
// `data-expr` attribute.

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


// Exercises
const exercise_1 = '{"type":"Impl","e1":{"type":"Var","name":"A"},"e2":{"type":"Impl","e1":{"type":"Var","name":"B"},"e2":{"type":"Var","name":"A"}}}';
const exercise_2 = '{"type":"Impl","e1":{"type":"False"},"e2":{"type":"Var","name":"A"}}';
const exercise_3 = '{"type":"Impl","e1":{"type":"Var","name":"A"},"e2":{"type":"Or","e1":{"type":"Var","name":"B"},"e2":{"type":"Var","name":"C"}}}';
const premises_3 = ['{"type":"Impl","e1":{"type":"Var","name":"A"},"e2":{"type":"Var","name":"B"}}'];
const exercise_4 = '{"type":"Var","name":"B"}';
const premises_4 = [
  '{"type":"Not","e":{"type":"Var","name":"C"}}',
  '{"type":"Impl","e1":{"type":"Not","e":{"type":"Var","name":"B"}},"e2":{"type":"Var","name":"C"}}',
];
const exercise_5 = '{"type":"Not","e":{"type":"And","e1":{"type":"Not","e":{"type":"Var","name":"A"}},"e2":{"type":"Var","name":"B"}}}';
const premises_5 = ['{"type":"Var","name":"A"}'];
const exercise_6 = '{"type":"Impl","e1":{"type":"Impl","e1":{"type":"Var","name":"A"},"e2":{"type":"Not","e":{"type":"Var","name":"A"}}},"e2":{"type":"Not","e":{"type":"Var","name":"A"}}}';
const exercise_7 = '{"type":"Iff","e1":{"type":"Impl","e1":{"type":"Var","name":"A"},"e2":{"type":"Var","name":"B"}},"e2":{"type":"Impl","e1":{"type":"Not","e":{"type":"Var","name":"B"}},"e2":{"type":"Not","e":{"type":"Var","name":"A"}}}}';

function make_exercise(objective, premises) {
  return {objective: objective, premises: premises, save_data: null};
}

var exercises_data = [
  make_exercise(exercise_1, []), make_exercise(exercise_2, []),
  make_exercise(exercise_3, premises_3), make_exercise(exercise_4, premises_4),
  make_exercise(exercise_5, premises_5), make_exercise(exercise_6, []),
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
      case "∀-elim":          return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "∃-intro":         return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
      case "∃-elim":          return { type: sep.children[1].innerHTML, subactions: gen_subactions() };
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
      "→-elim", "∀-elim", "∃-elim"
    ];

    switch (expr.type) {
      case "Var"   : break;
      case "False" : legal_moves += ["¬-elim"]; break;
      case "Not"   : legal_moves += ["¬-intro"]; break;
      case "And"   : legal_moves += ["∧-intro"]; break;
      case "Or"    : legal_moves += ["∨-intro-l", "∨-intro-r"]; break;
      case "Impl"  : legal_moves += ["→-intro"]; break;
      case "Iff"   : legal_moves += ["↔-intro"]; break;
      case "Forall": legal_moves += ["∀-intro"]; break;
      case "Exists": legal_moves += ["∃-intro"]; break;
    }

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
    && !is_legal_move(JSON.parse(focus.getAttribute("data-expr")), actions.type, actions.arg)
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
    case "∀-elim":          apply_rule("∀-elim", forall_elim); rebuild_children(); break;
    case "∃-elim":          apply_rule("∃-elim", exists_elim); rebuild_children(); break;
    case "¬-intro":         apply_rule("¬-intro", not_intro); rebuild_children(); break;
    case "∧-intro":         apply_rule("∧-intro", and_intro); rebuild_children(); break;
    case "∨-intro-l":       apply_rule("∨-intro-l", or_intro_l); rebuild_children(); break;
    case "∨-intro-r":       apply_rule("∨-intro-r", or_intro_r); rebuild_children(); break;
    // TODO
    case "∀-intro":         apply_rule("∀-intro", forall_intro); rebuild_children(); break;
    case "∃-intro":         apply_rule("∃-intro", exists_intro); rebuild_children(); break;
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
  EForall: (name, e) => ({ type: "Forall", name, e }),
  EExists: (name, e) => ({ type: "Exists", name, e }),
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
      next_token = tokens[pos];
      if (consume(')')) {
        return e;
      }
    } else if (next_token.type === Connective.FORALL || next_token.type === Connective.EXISTS) {
      const quantifier = next_token.type;
      pos++;
      next_token = tokens[pos];
      if (next_token && next_token.type === 'V') {
        const bound_var = next_token.value;
        pos++;
        next_token = tokens[pos];
        if (next_token && next_token.type === '.') {
          pos++;
          const e = parse_form();
          if (quantifier == Connective.FORALL) {
            return Expression.EForall(bound_var, e);
          } else {
            return Expression.EExists(bound_var, e);
          }
        }
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
      if (!t) { return null }
      if (!consume(')')) { return null; }
      return t;
    } else if (tokens[pos] && tokens[pos].type == 'V') {
      ++pos;
      return Expression.TVar(tokens[pos - 1].value);
    }
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

function apply_rule(name, rule_function, arg = null) {
  clear_above(focus);
  let expr = JSON.parse(focus.getAttribute("data-expr"));
  rule_function(expr, arg);
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
  open_input_panel(arg_input_string, () => apply_rule_with_arg_callback(name, input_callback));
}

function validate_or_input(parse_res) {
  switch (parse_res.type) {
    case "Or": return true;
    default  : input_panel_error.innerHTML = "Type error: Or-expression expected"; return false;
  }
}

function is_known(expr, node) {
  for (let i = 0; i < premises_holder.children.length; i++) {
    let p = premises_holder.children[i];
    if (p.getAttribute("data-expr") === expr) {
      return p;
    }
  }

  return null;
}

function update_known(node) {
  if (node.classList.contains("known")) {
    let known_cause = is_known(node.getAttribute("data-expr"), node);
    if (known_cause) {
      node.known = known_cause;
    }
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

// Called a bit too often, overkill (but performance is not an issue so who cares)
function recheck_status_of_tree(tree) {
  if (tree.known) {
    tree.known.removeAttribute("id");
  }
  set_focus(tree);
  let known = is_known(tree.getAttribute("data-expr"), tree);
  if (known) {
    tree.known = known;
    clear_above(tree);
    tree.classList.add("known");
    return true;
  }
  else {
    tree.known = null;
    tree.classList.remove("known");
  }

  if (!tree.parentNode.parentNode.classList.contains("subtree")) {
    return false;
  }

  let subtrees = tree.parentNode.parentNode.children[0].children;
  let success_for_all = true;
  if (subtrees.length === 0) { return false; }
  for (t of subtrees) {
    if (!recheck_status_of_tree(t.children[2].children[0])) {
      success_for_all = false;
    }
  }
  if (success_for_all) {
    tree.classList.add("known");
  }
  return success_for_all;
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

  switch (JSON.parse(focus.getAttribute("data-expr")).type) {
    case "Var"  : intro_rules_holder.innerHTML = ""; break;
    case "False": intro_rules_holder.innerHTML = not_elim; break;
    case "Not"  : intro_rules_holder.innerHTML = not_intro; break;
    case "And"  : intro_rules_holder.innerHTML = and_intro; break;
    case "Or"   : intro_rules_holder.innerHTML = or_intro_l + or_intro_r; break;
    case "Impl" : intro_rules_holder.innerHTML = impl_intro; break;
    case "Iff"  : intro_rules_holder.innerHTML = iff_intro; break;
  }

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
