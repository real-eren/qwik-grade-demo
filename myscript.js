
console.log("entered script");
const start_time = performance.now();


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// prepare lexer
// lexer consumes characters and yield tokens
// lexer is modeled as DFA.
// table of state transitions indexed by (state, char)
// some states are accepting - if no transition available, yields associated token (non-error)

// create lex token_ids with incrementing int keys
// NOTE:ORDER-SENSITIVE
let [TOK_ID, TOK_INT, TOK_STRING, TOK_REGEX_STRING, TOK_BOOL, TOK_CHAR,
  TOK_KEYWORD, TOK_LANG,
  TOK_QUOTE, TOK_QUASIQUOTE, TOK_DOT,
  TOK_LPAREN, TOK_LBRACE, TOK_LBRACKET,
  TOK_RPAREN, TOK_RBRACE, TOK_RBRACKET,
  TOK_BLOCK_COMMENT, TOK_LINE_COMMENT,
  TOK_WHITESPACE,
  TOK_ERROR, TOK_INCOMPLETE,
  ...LEFT_OVER_TOKS] = Array.from({length: 257}, (_, i) => i);
// over allocate at least one so that if LEFT_OVER_TOKS > 0 then previous toks have int
if (LEFT_OVER_TOKS.length === 0) { // could probably do this more precisely with a generator? doesn't really matter
  alert("did not allocate enough token ids");
}
const NUM_TOKENS = LEFT_OVER_TOKS[0];
const FIXED_TOKENS = new Map([[TOK_QUOTE, "'"], [TOK_QUASIQUOTE, "`"], [TOK_DOT, '.'], [TOK_LPAREN, '('], [TOK_RPAREN, ')'], [TOK_LBRACE, '{'], [TOK_RBRACE, '}'], [TOK_LBRACKET, '['], [TOK_RBRACKET, ']']]);
const DBG_TOKEN_NAME_BY_ID = {
  [TOK_ID]:"ID",
  [TOK_INT]:"INT",
  [TOK_STRING]:"STRING",
  [TOK_REGEX_STRING]:"REGEX_STRING",
  [TOK_BOOL]:"BOOL",
  [TOK_CHAR]:"CHAR",
  [TOK_KEYWORD]:"KEYWORD",
  [TOK_LANG]:"LANG",
  [TOK_QUOTE]:"QUOTE",
  [TOK_QUASIQUOTE]:"QUASIQUOTE",
  [TOK_DOT]:"DOT",
  [TOK_LPAREN]:"LPAREN",
  [TOK_LBRACE]:"LBRACE",
  [TOK_LBRACKET]:"LBRACKET",
  [TOK_RPAREN]:"RPAREN",
  [TOK_RBRACE]:"RBRACE",
  [TOK_RBRACKET]:"RBRACKET",
  [TOK_BLOCK_COMMENT]:"BLOCK_COMMENT",
  [TOK_LINE_COMMENT]:"LINE_COMMENT",
  [TOK_WHITESPACE]:"WHITESPACE",
  [TOK_ERROR]:"ERROR",
  [TOK_INCOMPLETE]:"INCOMPLETE",
};


const ASCII_COLLAPSED_CTRL_CHAR_MAX = 3; // should be at least 3. greater than 3 leaves unused code_units. those would be spooky.
const UNICODE1_CHAR_CODE = ASCII_COLLAPSED_CTRL_CHAR_MAX - 1;
const UNICODE2_CHAR_CODE = ASCII_COLLAPSED_CTRL_CHAR_MAX;
const COLLAPSED_ASCII_CTRL_CODE_UNIT = 0;
const ASCII_MAX = 127;

// called on code_unit (charCode) before looking up into state_jump_table
// assume well-formed text (no lone surrogates)
function normalize_code_unit(code_unit) {
  if (code_unit <= ASCII_COLLAPSED_CTRL_CHAR_MAX) {
    return COLLAPSED_ASCII_CTRL_CODE_UNIT;
  } else if (code_unit <= ASCII_MAX) {
    return code_unit;
  } else if (code_unit < 0xd800) {
    return UNICODE1_CHAR_CODE;
  } else {
    return UNICODE2_CHAR_CODE;
  }
}

const unicode = String.fromCharCode(UNICODE1_CHAR_CODE, UNICODE2_CHAR_CODE);

// common character classes
const CH_LC_ALPHA = "abcdefghijklmnopqrstuvwxyz";
const CH_UC_ALPHA = CH_LC_ALPHA.toUpperCase();
const CH_ALPHA = CH_LC_ALPHA + CH_UC_ALPHA;
const CH_DIGIT = "1234567890";
const CH_ALNUM = CH_ALPHA + CH_DIGIT;
const CH_WHITE_SPACE = " \t\n\f\r\v";
const CH_NON_DELIM = CH_ALNUM + "!@$%^&*_-+=:/?<>~" + unicode;
const CH_ALL = Array.from({length: 128}, (_, i) => String.fromCharCode(i)).join("");



/** non delim error rules */
const NDER = [[CH_NON_DELIM, 'error_until_delim'], ['\\', 'error_backslash'], ['|', 'error_pipe']];


/** special, unenterable state. used as jump state to explicitly REMOVE an edge */
const NULL_STATE = Symbol("null_state");

/** 
 * generate an array of consecutive states.
 * ex: for states '#fa' - '#fals'
 * ...state_chain('#fa' 'lse', '#F_or_false')
 * For use when creating the raw_state_table
 */
function state_chain(name_base, string, exit_state, case_sensitive=true) {
  return Array.from(string, (ch, i) => {
    let key = (case_sensitive) ? ch : (ch.toLowerCase() + ch.toUpperCase());
    let jump_state = (i === string.length - 1)
        ? exit_state
        : (name_base + string.substring(0, i+1));
    return [name_base + string.substring(0, i), new Map([...NDER, [key, jump_state]])];
  });
}

/** if present in a state rule table, that state is an accept state. val is the associated token_id */
const ACC_KEY = Symbol("accept");
/**
 * readable intermediate representation of state transition table
 * state table: state_name -> Rule table
 * Rule table: char class
 *           -> NULL_STATE
 *            | 'self'
 *            | state_name
 *            | token_id (shorthand for going to an unconditional accept state that returns that token_id)
 * Some rule tables may contain an ACC_KEY entry 
 * - this marks the state as an accept state
 * last rule for a character is kept
 * 'self' in RHS of rule is shorthand for parent state_name
 */
const raw_state_table = new Map([
  ['error_until_delim', new Map([
    [CH_NON_DELIM, 'self'],
    ['\\', 'error_backslash'],
    ['|', 'error_pipe'],
    [ACC_KEY, TOK_ERROR]
  ])],
  ['error_backslash', new Map([[CH_ALL, 'error_until_delim']])],
  ['error_pipe', new Map([[CH_ALL, 'self'], ['|', 'error_until_delim']])],


  ['initial', new Map([
    [CH_ALL, 'error_until_delim'],
    [CH_WHITE_SPACE, 'whitespace'],
    [CH_NON_DELIM, 'id'],
    [CH_DIGIT, 'int'],
    ['|', 'id_pipe'],
    ['+-', 'plus/minus'],
    ['\\', 'id_backslash'],
    ['#', '#'],
    [';', 'line_comment'],
    ['"', 'string_body'],
    ["'", TOK_QUOTE],
    ["`", TOK_QUASIQUOTE],
    ['.', 'dot'],
    ['(', TOK_LPAREN],
    [')', TOK_RPAREN],
    ['{', TOK_LBRACE],
    ['}', TOK_RBRACE],
    ['[', TOK_LBRACKET],
    [']', TOK_RBRACKET],
  ])],

  ['whitespace', new Map([
    [CH_WHITE_SPACE, 'self'],
    [ACC_KEY, TOK_WHITESPACE]
  ])],


  ['#', new Map([
    ...NDER,
    ['t', '#t'],
    ['T', '#T_or_true'],
    ['f', '#f'],
    ['F', '#F_or_false'],
    [':', 'keyword_body'],
    ['l', '#l'],
    ['r', '#r'],
    ['|', 'block_comment_body'],
    ['\\', 'char_start'],
  ])],

  ['#t', new Map([...NDER, ['r', '#tr'], [ACC_KEY, TOK_BOOL]])],
  ...state_chain('#tr', 'ue', '#T_or_true'),
  ['#T_or_true', new Map([...NDER, [ACC_KEY, TOK_BOOL]])],
  
  ['#f', new Map([...NDER, ['a', '#fa'], [ACC_KEY, TOK_BOOL]])],
  ...state_chain('#fa', 'lse', '#F_or_false'),
  ['#F_or_false', new Map([...NDER, [ACC_KEY, TOK_BOOL]])],

  ['keyword_body', new Map([
    [CH_NON_DELIM, 'self'],
    ['\\', 'keyword_backslash'],
    ['|', 'keyword_pipe'],
    [ACC_KEY, TOK_KEYWORD],
  ])],
  ['keyword_backslash', new Map([[CH_ALL, 'keyword_body']])],
  ['keyword_pipe', new Map([[CH_ALL, 'self'], ['|', 'keyword_body']])],

  ...state_chain('#l', 'ang', '#lang'),
  ['#lang', new Map([
    [CH_ALL, 'error_until_delim'],
    ...NDER,
    [' ', '#lang '], 
  ])],
  ['#lang ', new Map([
    ...NDER,
    [CH_ALNUM + "+-_/", 'lang_body']
  ])],
  ['lang_body', new Map([
    [CH_ALL, 'error_until_delim'],
    [CH_ALNUM + "+-_/", 'self'],
    [CH_WHITE_SPACE, NULL_STATE],// followed by whitespace: don't consume the char
    [ACC_KEY, TOK_LANG],
  ])],
  
  ...state_chain('#r', 'x"', 'regex_str'),
  ['regex_str', new Map([
    [CH_ALL, 'self'],
    ['\\', 'regex_str_backslash'],
    ['"', TOK_REGEX_STRING]
  ])],
  ['regex_str_backslash', new Map([[CH_ALL, 'regex_str']])],

  ['block_comment_body', new Map([
    [CH_ALL, 'self'],
    ['|', 'block_prev_was_pipe'],
  ])],
  ['block_prev_was_pipe', new Map([
    [CH_ALL, 'block_comment_body'],
    ['|', 'self'],
    ['#', TOK_BLOCK_COMMENT],
  ])],
  
  ['char_start', new Map([ // special chars: case-insensitive: newline, space, tab
    [CH_ALL, 'char_done'],
    ['sS', 'char_s'],
    ['nN', 'char_n'],
    ['tT', 'char_t'],
  ])],
  ['char_done', new Map([...NDER, [ACC_KEY, TOK_CHAR]])],
  ['char_s', new Map([...NDER, ['pP', 'char_sp'], [ACC_KEY, TOK_CHAR]])],
  ...state_chain('char_sp', 'ace', 'char_done', false),
  ['char_n', new Map([...NDER, ['eE', 'char_ne'], [ACC_KEY, TOK_CHAR]])],
  ...state_chain('char_ne', 'wline', 'char_done', false),
  ['char_t', new Map([...NDER, ['aA', 'char_ta'], [ACC_KEY, TOK_CHAR]])],
  ['char_ta', new Map([...NDER, ['bB', 'char_done']])],


  ['line_comment', new Map([
    [CH_ALL, 'self'],
    ['\n', TOK_LINE_COMMENT],
    [ACC_KEY, TOK_LINE_COMMENT]
  ])],


  ['plus/minus', new Map([
    [CH_NON_DELIM+'#', 'id'],
    ['|', 'id_pipe'],
    ['\\', 'id_backslash'],
    [CH_DIGIT, 'int'],
    [ACC_KEY, TOK_ID]
  ])],


  ['id_backslash', new Map([[CH_ALL, 'id']])],
  ['id', new Map([
    [CH_NON_DELIM + '#', 'self'],
    ['\\', 'id_backslash'],
    ['|', 'id_pipe'],
    [CH_WHITE_SPACE, NULL_STATE],
    [ACC_KEY, TOK_ID]
  ])],
  ['id_pipe', new Map([
    [CH_ALL, 'self'],
    ['|', 'id'],
  ])],


  ['string_body', new Map([
    [CH_ALL, 'self'],
    ['\\', 'string_backslash'],
    ['"', TOK_STRING],
  ])],
  ['string_backslash', new Map([[CH_ALL, 'string_body']])],

  ['dot', new Map([
    [CH_NON_DELIM + '#', 'id'],
    ['\\', 'id_backslash'],
    ['|', 'id_pipe'],
    [ACC_KEY, TOK_DOT]
  ])],

  ['int', new Map([
    [CH_NON_DELIM, 'id'],
    ['|', 'id_pipe'],
    ['\\', 'id_backslash'],
    [CH_DIGIT, 'self'],
    [ACC_KEY, TOK_INT]
  ])],
]);

// maps states (names) (excluding NULL_STATE) to lex token_ids (ints)
const raw_state_name_to_token_id = new Map();


// Pre-process raw_state_table
// this must be before any other code that reads from raw_state_table
// ensure that for every rule in every state, every jump is a valid value
for (const [state_name, state_jump_table] of raw_state_table.entries()) {
  for (const [key, jump_val] of state_jump_table.entries()) {
    if (key === ACC_KEY) {
      if (Number.isInteger(jump_val)) {
        raw_state_name_to_token_id.set(state_name, jump_val);
      } else {
        alert(`state ${state_name} has value ${jump_val} for accept token`);
      }
    }
    else if (jump_val === 'self') {
      state_jump_table.set(key, state_name);
    }
    else if (jump_val === NULL_STATE) {
      // do nothing
    }
    else if (typeof jump_val === 'string') {
      if (! (raw_state_table.has(jump_val))) {
        alert(`${state_name} references undeclared state '${jump_val}'`);
      } else {
        // ok
      }
    }
    else if (Number.isInteger(jump_val)) {
      let generated_accept_state_name = `gen_accept_${state_name}_${key}`;
      // now create accept state and register it.
      // replace int jump_val with name of genned state
      state_jump_table.set(key, generated_accept_state_name);
      raw_state_table.set(generated_accept_state_name, new Map());
      raw_state_name_to_token_id.set(generated_accept_state_name, jump_val);
    } else {
      alert(`did not handle ${key}, ${jump_val}`);
    }
  }
}

// plus one for implicit NULL_STATE;
const num_states = raw_state_table.size + 1; 
// using byte as jump_table value: if number of states > 255, complain!
// or just use 16 bit ints. duh
if (num_states > 255) {
  alert(`have ${num_states} states. can handle 255`);
}

// state_id to lex token_id
// by default, non-accepting -> produce TOK_INCOMPLETE. Entries for accepting states get overwritten later.
const accept_token_id_by_state_id = Array.from({length: num_states}, (_, i) => TOK_INCOMPLETE);


// index with (128 * state_id + 7bit charCode)
// where 128 is the range of supported ascii char codes
// value of 0 indicates no entry.
// given 0: accept if accept state, else error about incomplete token
const lex_jump_table = new Uint8Array(128 * num_states);

function calc_jump_table_idx(state_id, char_code) {
  return Math.imul(state_id , 128) + char_code;
}

const DBG_STATE_NAME_BY_ID = [NULL_STATE];
const NULL_STATE_ID = 0;
// associate unique int id to each state
// when compiling above raw state table to array tables, use byte val state_id in place of string 
const state_name_to_id = new Map([[NULL_STATE, NULL_STATE_ID]]);
{
  let state_idx = 1;
  for (const state_name of raw_state_table.keys()) {
    DBG_STATE_NAME_BY_ID[state_idx] = state_name;
    state_name_to_id.set(state_name, state_idx);
    state_idx += 1;
  }
}
const INITIAL_STATE_ID = state_name_to_id.get('initial');


// compile accept_states
for (const [state_name, token_id] of raw_state_name_to_token_id.entries()) {
  // ensure every accept state actually exists
  if (! (raw_state_table.has(state_name))) {
    alert(state_name + " entered as accept state, but does not exist");
  } else if (! Number.isInteger(token_id)) {
    alert(`${state_name} has non-int token_id: ${token_id}`);
  } else { // populate accept_token_id_by_state_id
    accept_token_id_by_state_id[state_name_to_id.get(state_name)] = token_id;
  }
}


// compile raw state table into array table
for (const [state, rules] of raw_state_table.entries()) {
  let state_id = state_name_to_id.get(state);

  for (const [key, jump] of rules.entries()) {
    let jump_id = state_name_to_id.get(jump);
    if (jump_id > num_states) {
      alert(`invalid jump id ${jump_id} for rule [${key}, ${jump}] in state ${state}.`);
    }
    for (let i = 0; i < key.length; ++i) {
      let ascii_code = key.charCodeAt(i);
      lex_jump_table[calc_jump_table_idx(state_id, ascii_code)] = jump_id;
    }
  }
}
// in order to avoid infinite loop, each call to lex must consume at least one token. 
// thus: initial state must have non-null for every entry
for (let i = 0; i < 128; ++i) {
  if (lex_jump_table[calc_jump_table_idx(INITIAL_STATE_ID, i)] === NULL_STATE_ID) {
    alert(`initial state is missing transition for code_unit ${i}!`);
  }
}

const NO_CLASS_STR = "";
const BUILTIN_MACRO_CLASS_STR = "rkt-macro";

/** 
 * Maps token_id to class name string.
 * empty str denotes DEFAULT color (black-ish for lightmode, white-ish for dark-mode)
 * Could use map instead of array but this gets called for EVERY token.
 */
const class_str_by_token_id = Array.from({length: NUM_TOKENS}, (_, i) => NO_CLASS_STR);
{ // don't pollute the namespace!
  function precompute(class_str, token_str) {
    return (class_str === NO_CLASS_STR) ? NO_CLASS_STR : `<span class="${class_str}">${token_str}</span>`;
  }

  const t = class_str_by_token_id;
  const id_class = "rkt-id";
  const comment_class = "rkt-cmnt";
  const paren_class = NO_CLASS_STR;
  const intish_literal_class = "rkt-int";
  const builtin_macro_class = BUILTIN_MACRO_CLASS_STR;
  const quote_class = builtin_macro_class;
  const str_class = "rkt-str";
  const error_class = "rkt-err";
  const keyword_class = "rkt-kw";
  t[TOK_ID] = id_class;
  t[TOK_INT] = intish_literal_class;
  t[TOK_STRING] = str_class;
  t[TOK_REGEX_STRING] = str_class;
  t[TOK_BOOL] = intish_literal_class;
  t[TOK_CHAR] = intish_literal_class;
  t[TOK_KEYWORD] = keyword_class;
  t[TOK_LANG] = NO_CLASS_STR;
  t[TOK_QUOTE] = quote_class;
  t[TOK_QUASIQUOTE] = quote_class;
  t[TOK_DOT] = NO_CLASS_STR;
  t[TOK_LPAREN] = paren_class;
  t[TOK_LBRACE] = paren_class;
  t[TOK_LBRACKET] = paren_class;
  t[TOK_RPAREN] = paren_class;
  t[TOK_RBRACE] = paren_class;
  t[TOK_RBRACKET] = paren_class;
  t[TOK_BLOCK_COMMENT] = comment_class;
  t[TOK_LINE_COMMENT] = comment_class;
  t[TOK_WHITESPACE] = NO_CLASS_STR; // will be handled specially anyway
  t[TOK_ERROR] = error_class;
  t[TOK_INCOMPLETE] = error_class;

  for (const [tok_id, tok_str] of FIXED_TOKENS.entries()) {
    t[tok_id] = precompute(t[tok_id], tok_str);
  }
}
/** Takes a non-empty span LHS string from and returns true if it's precomputed */
const SPAN_LHS_BY_TOKEN_ID = class_str_by_token_id.map(s => (s === NO_CLASS_STR || s[0] === '<') ? s : `<span class="${s}">`);

const NEWLINE_CHAR_CODE = '\n'.charCodeAt(0);

// some IDs belong to builtin macros, which get a special highlight
const BUILTIN_MACRO_NAME_TO_PRECOMPUTED_HTML = new Map([
  'require', 'provide', 'rename-out',
  'quote', 'quasiquote',
  'define', 'define-check',
  'test-begin', 'test-case', 'test-suite',
  'let', 'let*', 'letrec',
  'lambda', 'λ', 'case-lambda',
  'match', 'cond', 'case', 'if', 'or', 'and',
  'begin', 'begin0', 'when', 'unless',
  'set!',
  'module+', 'module*'
].map((name) => [name, `<span class="${BUILTIN_MACRO_CLASS_STR}">${name}</span>`]));


/**
 * Used in simple parser implementation
 */
const [PARSE_STATE_ERROR,
  PARSE_STATE_TOP_LEVEL,
  PARSE_STATE_EXPECT_DEFINE,
  PARSE_STATE_SKIP_LEFT_PARENS_UNTIL_ID,
  PARSE_STATE_APPEND_UNTIL_CLOSED,
  PARSE_STATE_SKIP_UNTIL_CLOSED] = [0, 1, 2, 3, 4, 5,];
const DBG_PARSE_STATE_TO_NAME = {
  [PARSE_STATE_ERROR]: 'PARSE_STATE_ERROR',
  [PARSE_STATE_TOP_LEVEL]: 'PARSE_STATE_TOP_LEVEL',
  [PARSE_STATE_EXPECT_DEFINE]: 'PARSE_STATE_EXPECT_DEFINE',
  [PARSE_STATE_SKIP_LEFT_PARENS_UNTIL_ID]: 'PARSE_STATE_SKIP_LEFT_PARENS_UNTIL_ID',
  [PARSE_STATE_SKIP_UNTIL_CLOSED]: 'PARSE_STATE_SKIP_UNTIL_CLOSED',
  [PARSE_STATE_APPEND_UNTIL_CLOSED]: 'PARSE_STATE_APPEND_UNTIL_CLOSED',
}

const PARSE_MODE_SNIPPET = Symbol("parse mode snippet");
const PARSE_MODE_WHOLE_FILE = Symbol("parse mode whole file");
/** 
 * based on parse_mode, returns either {
 *    pout_is_valid:
      pout_top_level_definitions: 
      pout_formatted_str:
 * } or ["lexemes"]
 * parse_mode = MODE_WHOLE_FILE | MODE_SNIPPET
 * 
 * Yes, this parse mode flag is evil but I don't yet know how to reuse the inner code
 * without making it significantly slower (would lean towards callbacks or pointers to a mutable state struct
 * but I have concerns about the performance of such a solution in JS).
 */
function parse_string(src_code_str, parse_mode) {
  const jump_table = lex_jump_table;

  var num_errors = 0;
  var num_fixed = 0;
  var num_other = 0;
  // current line of original source code.
  let line_count = 0;

  
  // stack of Left delimiters (paren | brace | bracket)
  // when parsing done, should return to this state
  const delim_stack = [TOK_INT]; // fill 0 slot so that checking last elem never returns `undefined`. also provides type hint
  function delim_stack_is_clear() { return delim_stack.length === 1; }

  let __encountered_delim_mismatch = false;
  function handle_delim_mismatch() {
    __encountered_delim_mismatch = true;
    current_parse_state = PARSE_STATE_ERROR;
  }


  // pointers to start and end of current token. inclusive, exclusive.
  let token_start_idx = 0;
  let token_end_idx = 0;

  function move_past_current_slice() {
    token_start_idx = token_end_idx;
  }
  function take_current_slice() {
    return src_code_str.substring(token_start_idx, token_end_idx);
  }

  // returns next token_id
  // start initial state
  function lex() {
    let current_state_id = INITIAL_STATE_ID;
    let next_state_id = INITIAL_STATE_ID;

    // pre-condition: token_end_idx points to the next character to be read.
    do {
      const char_code = normalize_code_unit(src_code_str.charCodeAt(token_end_idx));
      next_state_id = jump_table[calc_jump_table_idx(next_state_id, char_code)];
      if (next_state_id === NULL_STATE_ID) {
        // don't consume char! break loop to accept
        break;
      }

      token_end_idx += 1;
      current_state_id = next_state_id;

      if (char_code === UNICODE2_CHAR_CODE) {
        token_end_idx += 1;
      } else if (char_code === NEWLINE_CHAR_CODE) {
        line_count += 1;
      }
    } while (token_end_idx < src_code_str.length);

    // if was null_state_id, did NOT consume character

    return accept_token_id_by_state_id[current_state_id];
  }
  
  // append-only list of strings comprising the highlighted, formatted source code
  // array.join was measured (on firefox) to be at least as fast as string +=
  const formatted_string_buffer = [""];
  /** Given token type + string, appends HTML strings to buffer */
  // ex: <span style="color:#ff0000">January 30, 2011</span>
  function append_colorized_token(token_id, token_str, is_quoted_context) {
    const span_lhs = SPAN_LHS_BY_TOKEN_ID[token_id];
    if (span_lhs === NO_CLASS_STR) {
      formatted_string_buffer.push(token_str);
    } else if (span_lhs.at(-6) === '/') { // represents generic precomputed (quote, parens etc)
      formatted_string_buffer.push(span_lhs);
    } else {
      // if token_id === ID and token_str is builtin macro, use 
      if (token_id === TOK_ID && !is_quoted_context && BUILTIN_MACRO_NAME_TO_PRECOMPUTED_HTML.has(token_str)) {
        formatted_string_buffer.push(BUILTIN_MACRO_NAME_TO_PRECOMPUTED_HTML.get(token_str));
      } else {
        formatted_string_buffer.push(span_lhs, token_str, '</span>');
      }
    }
    // todo: add support for custom highlights
  }
  
  // log token frequency and match delimiters
  function handle_token(lex_tok_id) {
    // NOTE:ORDER-SENSITIVE
    // I sure hope the optimizer does its job transforming this into a jump table.
    switch (lex_tok_id) {
      case TOK_ID:
      case TOK_INT:
      case TOK_STRING:
      case TOK_REGEX_STRING:
      case TOK_BOOL:
      case TOK_CHAR:
      case TOK_KEYWORD:
      case TOK_LANG:
        num_other += 1;
        break;
      case TOK_QUOTE:
      case TOK_QUASIQUOTE:
      case TOK_DOT:
        num_fixed += 1;
        break;
      case TOK_LPAREN:
      case TOK_LBRACE:
      case TOK_LBRACKET:
        delim_stack.push(lex_tok_id);
        // increase indent?
        num_fixed += 1;
        break;
      case TOK_RPAREN:
        if (delim_stack.at(-1) === TOK_LPAREN) {
          delim_stack.pop();
        } else {
          handle_delim_mismatch();
          // error. highlight different
        }
        num_fixed += 1;
        break;
      case TOK_RBRACE:
        if (delim_stack.at(-1) === TOK_LBRACE) {
          delim_stack.pop();
        } else {
          handle_delim_mismatch();
        }
        num_fixed += 1;
        break;
      case TOK_RBRACKET:
        if (delim_stack.at(-1) === TOK_LBRACKET) {
          delim_stack.pop();
        } else {
          handle_delim_mismatch();
        }
        num_fixed += 1;
        break;
      case TOK_BLOCK_COMMENT:
      case TOK_LINE_COMMENT:
        num_other +=1;
        break; // don do nothin for comments
      case TOK_WHITESPACE:
        num_fixed += 1;
        break; //
      case TOK_ERROR:
      case TOK_INCOMPLETE:
        break;
      default:
        alert(`uhoh! unhandled token :( val '${DBG_TOKEN_NAME_BY_ID[lex_tok_id]}' at line ${line_count}, token_end_idx = ${token_end_idx}`);
    }
  }


  // name -> { str: string, tokens: array of token str slices (excluding whitespace and comments) }
  const top_level_definitions = new Map();
  // modified by handle_token
  // reassigned to new empty array after finishing an expr.
  let current_top_level_expr_tokens;
  let current_top_level_expr_start_idx;
  let current_top_level_define_name;
  let current_parse_state;
  function initialize_parse_state() {
    current_top_level_expr_tokens = ['(', 'define'];
    current_top_level_define_name = '';
    current_parse_state = PARSE_STATE_TOP_LEVEL;
    current_top_level_expr_start_idx = token_start_idx;
  }

  // this is more nicely written as a coroutine but JS's iterators have too much overhead
  // handle_token() will detect if delimiters don't match
  function simple_parse_step(tok_id, tok_slice) {
    switch (current_parse_state) {
      case PARSE_STATE_ERROR:
        // mismatched delimiters, do nothing for rest of file.
        return;
      case PARSE_STATE_TOP_LEVEL:
        if (tok_id === TOK_LPAREN || tok_id === TOK_LBRACE || tok_id === TOK_LBRACKET) {
          current_top_level_expr_start_idx = token_start_idx-1;
          current_parse_state = PARSE_STATE_EXPECT_DEFINE;
        }
        // else skip, stay in top_level
        break;
      case PARSE_STATE_EXPECT_DEFINE:
        switch (tok_id) {
          case TOK_WHITESPACE:
          case TOK_LINE_COMMENT:
          case TOK_BLOCK_COMMENT:
            break;
          case TOK_ID:
            if (tok_slice === 'define') {
              current_parse_state = PARSE_STATE_SKIP_LEFT_PARENS_UNTIL_ID;
              break;
            }
          default:
            current_parse_state = PARSE_STATE_SKIP_UNTIL_CLOSED;
        }
        break;
      case PARSE_STATE_SKIP_LEFT_PARENS_UNTIL_ID:
        switch (tok_id) {
          case TOK_WHITESPACE:
          case TOK_LINE_COMMENT:
          case TOK_BLOCK_COMMENT:
            break; // skip
          case TOK_LPAREN:
          case TOK_LBRACE:
          case TOK_LBRACKET:
            current_top_level_expr_tokens.push('(');
            break;
          case TOK_ID:
            current_top_level_expr_tokens.push(tok_slice);
            current_top_level_define_name = tok_slice;
            current_parse_state = PARSE_STATE_APPEND_UNTIL_CLOSED;
            break
          default:
            current_parse_state = PARSE_STATE_SKIP_UNTIL_CLOSED;
        }
        break;
      case PARSE_STATE_APPEND_UNTIL_CLOSED:
        switch (tok_id) {
          case TOK_WHITESPACE:
          case TOK_LINE_COMMENT:
          case TOK_BLOCK_COMMENT:
            break;
          case TOK_LBRACE:
          case TOK_LPAREN:
          case TOK_LBRACKET:
            current_top_level_expr_tokens.push('(');
            break;
          case TOK_RBRACE:
          case TOK_RPAREN:
          case TOK_RBRACKET:
            current_top_level_expr_tokens.push(')');
            break;
          default:
            current_top_level_expr_tokens.push(tok_slice);
        }
        if (delim_stack_is_clear()) {
          top_level_definitions.set(
            current_top_level_define_name,
            {
              str: src_code_str.substring(current_top_level_expr_start_idx, token_end_idx),
              tokens: current_top_level_expr_tokens
            });
          initialize_parse_state();
        } // else stay in state
        break;
      case PARSE_STATE_SKIP_UNTIL_CLOSED:
        if (delim_stack_is_clear()) {
          current_parse_state = PARSE_STATE_TOP_LEVEL;
        } // else stay in state
        break;
      default:
        alert(`parse state not handled!: ${current_parse_state}. tok_id = ${tok_id}`)
        break;
    }
  }

  function parse_whole_file() {
    initialize_parse_state();
    while (token_end_idx < src_code_str.length) {
      const tok_id = lex();

      handle_token(tok_id);
      const tok_str = take_current_slice(); // future: maybe skip for fixed tokens
      move_past_current_slice();

      // builds top-level def map
      simple_parse_step(tok_id, tok_str);
      // highlighting without formatting
      append_colorized_token(tok_id, tok_str, false);
    }
  }
  function parse_snippet() {
    const lexemes = [];
    while (token_end_idx < src_code_str.length) {
      const tok_id = lex();
      switch (tok_id) {
        case TOK_LINE_COMMENT:
        case TOK_BLOCK_COMMENT:
        case TOK_WHITESPACE:
          break;
        case TOK_LPAREN:
        case TOK_LBRACE:
        case TOK_LBRACKET:
          lexemes.push('(');
          break;
        case TOK_RPAREN:
        case TOK_RBRACE:
        case TOK_RBRACKET:
          lexemes.push(')');
          break;
        default:
          lexemes.push(take_current_slice());
          break;
      }
      move_past_current_slice();
    }
    return lexemes;
  }

  if (parse_mode === PARSE_MODE_WHOLE_FILE) {
    parse_whole_file();
    const out_str = formatted_string_buffer.join('');
    console.log(`parsed string with ${src_code_str.length} bytes, ${line_count} lines,
      ${num_errors} errors, ${formatted_string_buffer.length} html snippets,
      ${num_fixed} fixed tokens, ${num_other} other tokens,
      total formatted length = ${out_str.length}
      `);

    let WIP_output = {
      // prefix so that autocomplete is actually useful
      pout_is_valid: !__encountered_delim_mismatch,
      pout_top_level_definitions: top_level_definitions,
      pout_formatted_str: out_str
    };
    return WIP_output;
  } else if (parse_mode === PARSE_MODE_SNIPPET) {
      return parse_snippet();
  } else {
    alert(`invalid parse_mode: ${parse_mode}`);
  }

} // end parse_string

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
console.log(`computing lexer took ${performance.now() - start_time} milliseconds`);


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// LEXEME TRIE IMPL

const TRIE_LEAF_KEY = Symbol("trie leaf key");

// unbalanced tree where path is the key.
// leaf nodes are sets of values
function add_seq_to_trie(trie, lexeme_seq, value) {
  const num_lexemes = lexeme_seq.length;
  if (num_lexemes === 0) {
    alert(`(clown behavior detected): tried to insert empty seq into trie. Value: ${value}`);
    return;
  }
  let cur_node = trie;
  for (let i = 0; i < num_lexemes; ++i) {
    const lexeme = lexeme_seq[i];
    if (cur_node.has(lexeme)) {
      cur_node = cur_node.get(lexeme);
    } else { // add rest of seq to trie (all new entries)
      for (; i < num_lexemes; ++i) {
        const lexeme = lexeme_seq[i];
        const new_node = new Map();
        cur_node.set(lexeme, new_node);
        cur_node = new_node;
      }
      // implicitly ends outer loop
    }
  }
  // cur_node now points to parent of leaf node
  // finished lex seq, add value as leaf
  if (! cur_node.has(TRIE_LEAF_KEY)) {
    cur_node.set(TRIE_LEAF_KEY, new Set());
  }
  cur_node.get(TRIE_LEAF_KEY).add(value);
}

// normally, you would pass a top-level definition to this
// those are assumed to be valid by the time you call this
function add_deep_seq_to_trie(trie, lexeme_seq, value) {
  const node_stack = (lexeme_seq[0] === '(') ? [] : [trie];
  const num_lexemes = lexeme_seq.length;
  for (let lex_i = 0; lex_i < num_lexemes; ++lex_i) {
    const lexeme = lexeme_seq[lex_i];
    if (lexeme === '(') {
      node_stack.push(trie);
    }

    // for each node on stack, push
    for (let node_i in node_stack) {
      const node = node_stack[node_i];
      if (node.has(lexeme)) {
        // do nothing
      } else {
        node.set(lexeme, new Map());
      }
      node_stack[node_i] = node.get(lexeme);
    }

    if (lexeme === ')') {
      // insert val to ACC for last seq's node
      const last_node = node_stack.pop();
      if (! last_node.has(TRIE_LEAF_KEY)) {
        last_node.set(TRIE_LEAF_KEY, new Set());
      }
      last_node.get(TRIE_LEAF_KEY).add(value);
    }
  }
}

// returns set of values or false
function lookup_in_trie(trie, lexeme_seq) {
  const num_lexemes = lexeme_seq.length;
  if (num_lexemes === 0) {
    alert(`(clown behavior detected): tried to insert empty seq into trie. Trie: ${trie}`);
    return false;
  }
  let cur_node = trie;
  for (let i = 0; i < num_lexemes; ++i) {
    const lexeme = lexeme_seq[i];
    if (cur_node.has(lexeme)) {
      cur_node.get(lexeme);
    } else return false;
  }
  // cur_node points to parent of leaf node
  return (cur_node.has(TRIE_LEAF_KEY))
    ? cur_node.get(TRIE_LEAF_KEY)
    : false;
}

// takes two tries and passes parallel leaf nodes to the call_back
// callstack as deep as the longest sequence
// can use explicit stack of iterators instead (not as cool but can handle longer seqs)
// seems most browser support call stacks in the thousands
function match_tries(trie1, trie2, pair_callback) {
  // iterate over entries in a, lookup in b.
  // a should be the smaller (fewer entries) map
  const swapped = (trie2.size < trie1.size);
  let [a, b] = (swapped) 
    ? [trie2, trie1]
    : [trie1, trie2];

  for (const [key, a_val] of a) {
    const b_val = b.get(key);
    if (b_val === undefined) continue;
    else if (key === TRIE_LEAF_KEY) {
      if (swapped) pair_callback(b_val, a_val);
      else pair_callback(a_val, b_val);
    } else 
      if (swapped) match_tries(b_val, a_val, pair_callback);
      else match_tries(a_val, b_val, pair_callback);
  }
  // elegant!
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


// all the uploaded files
let uploaded_files = [];
function get_current_file() { return (uploaded_files.length === 0) ? null : uploaded_files[doc_current_file_name_dropdown.selectedIndex]; }

const filename_to_file = new Map();
const filename_to_original_text = new Map();
// currently only '.rkt' files
const filename_to_html = new Map();
const filename_to_top_level_defs = new Map();
const filename_to_trie = new Map();

/** name -> ['comments'] */
const group_name_to_comments = new Map();
// double index to make lookups in both directions faster
// "name" -> set{ 'groupnames' }
const filename_to_groups = new Map();
// "name" -> set{ 'filenames' }
const group_to_filenames = new Map();
// "name" -> list of file-specific comments
const filename_to_comments = new Map();

// "name" -> [lexemes]
// only for groups made from snippets in supported formats (Racket atm)
const group_name_to_seq = new Map();
const group_name_to_snippet = new Map();

// trie of group seqs to group names
const combined_group_trie = new Map();

// used after deleting a group
function recalculate_combined_group_trie() {
  const trie = combined_group_trie; // just a local binding of global var, 
  trie.clear();
  for (const [group_name, seq] of group_name_to_seq.entries()) {
    add_seq_to_trie(trie, seq, group_name);
  }
}

// compensating for the annoying behavior of .value and .textContent for select>option
const selected_group_name_array = ["Just this file"]
function get_selected_groupname() {
  return selected_group_name_array[current_group_dropdown.selectedIndex];
}


function add_filename_to_group(filename, groupname) {
  group_to_filenames.get(groupname).add(filename);
  filename_to_groups.get(filename).add(groupname);
}

function remove_filename_from_group(filename, groupname) {
  group_to_filenames.get(groupname).delete(filename);
  filename_to_groups.get(filename).delete(groupname);
}

const groupname_keyed_maps = [group_to_filenames, group_name_to_comments, group_name_to_snippet, group_name_to_seq];
function unlink_group(group_name) {
  for (const filename of group_to_filenames.get(group_name).values()) {
    filename_to_groups.get(filename).delete(group_name);
  }
  for (const map of groupname_keyed_maps) {
    map.delete(group_name);
  }
  const idx = current_match_suggestions.findIndex( (e) => e[0] === group_name );
  if (idx !== -1) {
    current_match_suggestions.splice(idx, 1);
  }
  // combined_group_trie gets recalculated by the code that called this function
}

const filename_keyed_maps = [filename_to_comments, filename_to_html, filename_to_file, filename_to_trie, filename_to_original_text, filename_to_top_level_defs, filename_to_groups];
function unlink_file(filename) {
  if (! filename.endsWith(".rkt")) return; // todo: generalize
  for (const groupname of filename_to_groups.get(filename).values()) {
    group_to_filenames.get(groupname).delete(filename);
  }
  for (const map of filename_keyed_maps) {
    map.delete(filename);
  }
  if (filename === last_file_for_suggestions) {
    // clear suggestions
    last_file_for_suggestions = undefined;
    current_match_suggestions.length = 0;
    update_ui_for_suggestions();
  }
}


const doc_new_group_name_input = document.getElementById("new_group_name_input");
const create_group_button = document.getElementById("create_group_button");
const current_group_dropdown = document.getElementById("current_group_dropdown");
doc_new_group_name_input.addEventListener("change", (event) => {
  const new_name = doc_new_group_name_input.value;
  create_group_button.disabled = (new_name === "" || group_name_to_comments.has(new_name));
});
create_group_button.addEventListener("click", (event) => {
  const new_name = doc_new_group_name_input.value;
  if (new_name === "") return;
  if (group_name_to_comments.has(new_name)) {
    alert("group already exists");
    return;
  }
  const new_option = document.createElement("option");
  new_option.text = new_name;


  current_group_dropdown.add(new_option);
  selected_group_name_array.push(new_name);
  current_group_dropdown.selectedIndex = current_group_dropdown.options.length - 1;

  group_name_to_comments.set(new_name, []);
  group_to_filenames.set(new_name, new Set());

  if (selection_type_dropdown.value === "Racket") {
    const snippet = doc_selected_text.value;
    if (snippet.length !== 0) {
      const seq = parse_string(snippet, PARSE_MODE_SNIPPET);
      group_name_to_snippet.set(new_name, snippet);
      group_name_to_seq.set(new_name, seq);
      add_seq_to_trie(combined_group_trie, seq, new_name);
    }
  }

  doc_new_group_name_input.value = "";
  update_ui_for_current_group();
  update_ui_for_current_file();
});

function set_group_button_mode(new_mode) {
  __group_button_mode = new_mode;
  if (new_mode === REMOVE_FROM_GROUP_MODE) {
    add_to_group_button.textContent = "Remove file from group";
  } else if (new_mode === ADD_TO_GROUP_MODE) {
    add_to_group_button.textContent = "Add file to group";
  } else {
    console.log(`clown behavior detected: tried to set group button to mode "${new_mode}"`);
  }
}
current_group_dropdown.addEventListener("change", (event) => {
  if (uploaded_files.length !== 0) {
    // if file in group, set mode to remove from group
    // else set to add to group
    const cur_filename = get_current_file().name;
    if (current_group_dropdown.selectedIndex !== 0) {
      const cur_groupname = get_selected_groupname();
      set_group_button_mode((group_to_filenames.get(cur_groupname).has(cur_filename))
          ? REMOVE_FROM_GROUP_MODE
          : ADD_TO_GROUP_MODE);
    }
  }
  update_ui_for_current_group();
});

const delete_group_button = document.getElementById("delete_group_button");
delete_group_button.addEventListener("click", (event) => {
  const idx = current_group_dropdown.selectedIndex;
  if (idx == 0) return;
  const old_group_name = get_selected_groupname();
  current_group_dropdown.remove(idx);
  selected_group_name_array.splice(idx, 1);
  current_group_dropdown.selectedIndex = idx - 1;
  unlink_group(old_group_name);
  update_ui_for_current_group();
});

function update_ui_for_current_group() {
  const idx = current_group_dropdown.selectedIndex;
  const no_files_uploaded = uploaded_files.length === 0;
  delete_group_button.disabled = (idx === 0);
  add_to_group_button.disabled = (no_files_uploaded || idx === 0);
  if (idx === 0) {
    scroll_div_for_comments.p;
  } else {
    // if in group mode, lookup
    scroll_div_for_comments
  }
  update_ui_for_comment();
  update_ui_for_group_membership();
  update_ui_for_comment_display();
}

const ADD_TO_GROUP_MODE = Symbol("add to group mode");
const REMOVE_FROM_GROUP_MODE = Symbol("remove from group mode");
let __group_button_mode = ADD_TO_GROUP_MODE;
const add_to_group_button = document.getElementById("add_to_group_button");
add_to_group_button.addEventListener("click", (event) => {
  if (uploaded_files.length === 0) return;
  const cur_filename = get_current_file().name;
  const selected_group_index = current_group_dropdown.selectedIndex;
  if (selected_group_index === 0) return;
  const selected_group_name = get_selected_groupname();
  if (__group_button_mode === ADD_TO_GROUP_MODE) {
    // can't be N/A group
    // ignore if already in group
    if (filename_to_groups.get(cur_filename).has(selected_group_name)) {
      // do nothing
    } else {
      add_filename_to_group(cur_filename, selected_group_name);
      set_group_button_mode(REMOVE_FROM_GROUP_MODE);
    }
    set_group_button_mode(REMOVE_FROM_GROUP_MODE);
  } else if (__group_button_mode === REMOVE_FROM_GROUP_MODE) {
    remove_filename_from_group(cur_filename, selected_group_name);
    set_group_button_mode(ADD_TO_GROUP_MODE);
  } else {
    alert(`unhandled group button mode: ${__group_button_mode}`);
  }
  update_ui_for_group_membership();
});


const doc_divtext = document.getElementById('divtext');
const doc_current_file_text_div = document.getElementById("current_file_name_div");
const prev_file_button = document.getElementById("prev_file_button");
const doc_current_file_name_dropdown = document.getElementById("current_file_name_drop_down");
const next_file_button = document.getElementById("next_file_button");
function update_ui_for_comment() {
  submit_comment_button.disabled = (doc_comment_text.value === "" || (current_group_dropdown.selectedIndex === 0 && uploaded_files.length === 0));
}
function update_ui_for_current_file() {
  update_ui_for_comment();
  update_ui_for_group_membership();
  update_ui_for_comment_display();
  update_ui_for_suggestions();
  const no_files_uploaded = uploaded_files.length === 0;
  const new_name = doc_new_group_name_input.value;
  create_group_button.disabled = (new_name === "" || group_name_to_comments.has(new_name));
  remove_current_file_button.disabled = next_file_button.disabled = prev_file_button.disabled = no_files_uploaded;
  lookup_definition_button.disabled = true; // re-enable below IFF current file is .rkt
  if (no_files_uploaded) {
    add_to_group_button.disabled = true;
    doc_divtext.innerHTML = "\n    nothing loaded <span style='color:red;'>yet</span> =)";
    doc_current_file_text_div.textContent = "No file selected";
    selection_type_dropdown.value = "";
  } else {
    add_to_group_button.disabled = current_group_dropdown.selectedIndex === 0;
    // get parsed_str_html for current file
    const current_file_name = get_current_file().name;
    doc_current_file_text_div.textContent = current_file_name;
    if (filename_to_html.has(current_file_name)) {
      doc_divtext.innerHTML = filename_to_html.get(current_file_name);
      selection_type_dropdown.selectedIndex = 1; // implicitly ends with ".rkt"
      lookup_definition_button.disabled = false;
    } else {
      doc_divtext.textContent = filename_to_original_text.get(current_file_name);
      selection_type_dropdown.selectedIndex = 0;
    }
  }
}


prev_file_button.addEventListener("click", (event) => {
  const current_file_index = doc_current_file_name_dropdown.selectedIndex;
  doc_current_file_name_dropdown.selectedIndex = (current_file_index > 0) ? current_file_index - 1 : uploaded_files.length-1;
  update_ui_for_current_file();
});

next_file_button.addEventListener("click", (event) => {
  const current_file_index = doc_current_file_name_dropdown.selectedIndex;
  doc_current_file_name_dropdown.selectedIndex = (current_file_index < uploaded_files.length-1) ? current_file_index+1 : 0;
  update_ui_for_current_file();
});

doc_current_file_name_dropdown.addEventListener("change", (event) => {
  update_ui_for_current_file();
});

const remove_all_files_button = document.getElementById("remove_all_files_button");
remove_all_files_button.addEventListener("click", (event) => {
  uploaded_files.length = 0;
  filename_to_file.clear();
  filename_to_original_text.clear();
  filename_to_html.clear();
  filename_to_comments.clear();
  doc_current_file_name_dropdown.options.length = 0;
  update_ui_for_current_file();
});

const remove_current_file_button = document.getElementById("remove_current_file_button");
remove_current_file_button.addEventListener("click", (event) => {
  if (uploaded_files.length === 0) return;
  const current_file_index = doc_current_file_name_dropdown.selectedIndex;
  const removed_file = get_current_file().name;
  uploaded_files.splice(current_file_index, 1);
  unlink_file(removed_file);
  doc_current_file_name_dropdown.remove(current_file_index);
  update_ui_for_current_file();
});

const doc_filepicker = document.getElementById('upload_button');
doc_filepicker.addEventListener("change", (event) => { 
  if (!window.FileReader) {
    alert("your browser does not seem to support uploading files? (Window.FileReader)");
    return;
  }
  const new_files = event.target.files;
  for (const file of new_files) {
    let fname = file.name;
    // skip those whose lastModified field is redundant
    if (! filename_to_file.has(fname)
        || filename_to_file.get(fname).lastModified < file.lastModified) {
      uploaded_files.push(file);
      { 
        let option = document.createElement("option");
        option.text = file.name;
        doc_current_file_name_dropdown.add(option);
      }

      filename_to_file.set(fname, file);
      filename_to_groups.set(fname, new Set());
      filename_to_comments.set(fname, []);

      let reader = new FileReader();
      reader.addEventListener(
        "load",
        (load_event) => {
          if (load_event.target.readyState != 2) return;
          if (load_event.target.error) {
            alert('Error while reading file: ' + fname);
            return;
          }

          const file_content = reader.result;
          filename_to_original_text.set(fname, file_content);

          if (fname.endsWith(".rkt")) {
            const start_time = performance.now();
            const parser_output = parse_string(file_content, PARSE_MODE_WHOLE_FILE);
            let stop = performance.now();
            console.log(`finished lexing in just ${stop - start_time} milliseconds`);

            let parsed_str_html = parser_output.pout_formatted_str;
            filename_to_html.set(fname, parsed_str_html);
            const top_level_definitions = parser_output.pout_top_level_definitions;
            filename_to_top_level_defs.set(fname, top_level_definitions);

            const trie = new Map();
            for (const [funcname, v] of top_level_definitions.entries()) {
              // v is { str: , tokens: }
              add_deep_seq_to_trie(trie, v.tokens, funcname);
            }
            filename_to_trie.set(fname, trie);
          }
          if (file === new_files[0]) {
            update_ui_for_current_file();
            update_ui_for_current_group();
          }
        }, false
      );
      reader.readAsText(file);
    }

  } // end for
});

// returns the text selected by a user's click and drag.
function get_highlighted_text() {
  return (window.getSelection)
    ? window.getSelection().toString()
    : "";
}

const doc_selected_text = document.getElementById("selected_text");
let selected_text_lock = false;
document.onselectionchange = function() {
  if (!selected_text_lock) {
    doc_selected_text.value = get_highlighted_text();
  }
};

const lock_selection_button = document.getElementById("lock_selection_button");
function set_selection_lock(new_state) {
  selected_text_lock = new_state;
  lock_selection_button.textContent = (selected_text_lock) ? "unlock selection" : "lock selection";
}
lock_selection_button.addEventListener("click", (event) => {
  set_selection_lock(!selected_text_lock);
});

const lookup_definition_button = document.getElementById("lookup_definition_button");
lookup_definition_button.addEventListener("click", (event) => {
  const current_file = get_current_file();
  if (!current_file || !filename_to_top_level_defs.has(current_file.name)) return;
  const def_map = filename_to_top_level_defs.get(current_file.name);
  const old_selected_text = doc_selected_text.value;
  if (def_map.has(old_selected_text)) {
    doc_selected_text.value = def_map.get(old_selected_text).str;
    set_selection_lock(true);
  }
});

const selection_type_dropdown = document.getElementById("selection_type_dropdown");

const doc_comment_text = document.getElementById("comment_text");
const submit_comment_button = document.getElementById("submit_comment_button");
doc_comment_text.addEventListener("change", (event) => {
  update_ui_for_comment();
});
submit_comment_button.addEventListener("click", (event) => {
  const comment_text = doc_comment_text.value;
  if (comment_text === "") return;
  const cur_groupname = get_selected_groupname();
  // if group index == 0, specific to file
  // also, if group idx is 0, this button is disabled if no files uploaded
  if (current_group_dropdown.selectedIndex === 0) {
    const cur_filename = get_current_file().name;
    filename_to_comments.get(cur_filename).push(comment_text);
    update_ui_for_group_membership();
  } else {
    group_name_to_comments.get(cur_groupname).push(comment_text);
  }
  update_ui_for_comment_display();
  doc_comment_text.value = "";
});

const COMMENT_DISPLAY_MODE_FILE = 0;
const COMMENT_DISPLAY_MODE_GROUP = 1;
const comment_display_mode_dropdown = document.getElementById("comment_display_mode_dropdown");
const scroll_div_for_comments = document.getElementById("scroll_div_for_comments");

function update_ui_for_comment_display() {
  const is_file_mode = (comment_display_mode_dropdown.selectedIndex === COMMENT_DISPLAY_MODE_FILE);
  const cur_filename = get_current_file()?.name;
  let all_comments;
  if (comment_display_mode_dropdown.selectedIndex === COMMENT_DISPLAY_MODE_FILE) {
    all_comments = [];
    if (uploaded_files.length === 0) {
      // do nothing
    } else {
      // concat comments from all groups this file belongs to + 'just this file'
      for (const groupname of filename_to_groups.get(cur_filename)?.values() ?? []) {
        for (const comment of group_name_to_comments.get(groupname)) {
          all_comments.push(comment);
        }
      }
      for (const comment of filename_to_comments.get(cur_filename) ?? []) {
        all_comments.push(comment);
      }
    }
  } else { // for group
    if (current_group_dropdown.selectedIndex === 0) { // group is 'Just this file'
      all_comments = filename_to_comments.get(cur_filename) ?? [];
    } else {
      all_comments = group_name_to_comments.get(get_selected_groupname());
    }
  }
  // wrap each comment in '' and separate with 2 newlines
  scroll_div_for_comments.textContent = (all_comments.length === 0) ? "" : ("'" + all_comments.join("'\n\n'") + "'");
}

comment_display_mode_dropdown.addEventListener("change", (event) => {
  update_ui_for_comment_display();
});

const GROUP_MEMBERSHIP_MODE_FOR_FILE = 0;
const GROUP_MEMBERSHIP_MODE_FOR_GROUP = 1;
const file_group_membership_mode_dropdown = document.getElementById("file_group_membership_mode_dropdown");
const scroll_div_for_file_group_membership = document.getElementById("scroll_div_for_file_group_membership");

function update_ui_for_group_membership() {
  const is_for_file_mode = file_group_membership_mode_dropdown.selectedIndex === GROUP_MEMBERSHIP_MODE_FOR_FILE;
  const cur_filename = get_current_file()?.name;
  let name_iter;
  if (is_for_file_mode) {
    // list groups belonging to this file
    name_iter = filename_to_groups.get(cur_filename)?.values() ?? [];
  } else {
    // list files belonging to this group
    // but if group is 'just this file', list files that DO have entries.
    if (current_group_dropdown.selectedIndex === 0) {
    const es = filename_to_comments.entries();
    name_iter = Array.from(es).filter((e) => e[1].length !== 0).map((e) => e[0]);
    } else {
      name_iter = group_to_filenames.get(get_selected_groupname())?.values() ?? [];
    }
  }
  const all_names = Array.from(name_iter);
  scroll_div_for_file_group_membership.textContent = (all_names.length === 0) ? "" : ("'" + all_names.join("'\n\n'") + "'");
}

file_group_membership_mode_dropdown.addEventListener("change", (event) => {
  update_ui_for_group_membership();
});

const find_matches_button = document.getElementById("find_matches_button");
const reject_match_button = document.getElementById("reject_match_button");
const accept_match_button = document.getElementById("accept_match_button");
// name of the file for which the existing suggestions apply to. (used when deleting a file)
let last_file_for_suggestions = undefined;
const doc_file_name_for_suggestions = document.getElementById("file_name_for_suggestions");
const match_snippets_label = document.getElementById("match_snippets_label");
const scroll_div_for_match_snippet = document.getElementById("scroll_div_for_match_snippet");
const scroll_div_for_func_name_list = document.getElementById("scroll_div_for_func_name_list");
const current_match_suggestions = [];

find_matches_button.addEventListener("click", (event) => {
  if (uploaded_files.length === 0) return;
  const cur_filename = get_current_file().name;
  // todo: generalize
  if (! cur_filename.endsWith(".rkt")) return;

  last_file_for_suggestions = cur_filename;
  current_match_suggestions.length = 0;
  const file_trie = filename_to_trie.get(cur_filename);
  if (file_trie === undefined) console.log("clown behavior detected: didn't filter out file without trie");

  const group_set_for_current_file = filename_to_groups.get(cur_filename);

  // matched groups -> definitions in file that contained the matching snippet
  const group_to_func_names = new Map();
  const match_result_callback = (func_names, groupnames) => {
    for (const groupname of groupnames.values()) {
      if (group_set_for_current_file.has(groupname)) continue;
      const group_set = new Set();
      group_to_func_names.set(groupname, group_set);
      for (const func_name of func_names.values()) {
        group_set.add(func_name);
      }
    }
  };
  match_tries(file_trie, combined_group_trie, match_result_callback);
  
  // add results grouped by group
  for (const [group, func_names] of group_to_func_names.entries()) {
    current_match_suggestions.push([group, func_names]);
  }
  if (current_match_suggestions.length === 0) {
    doc_file_name_for_suggestions.textContent = "N/A";
  } else {
    doc_file_name_for_suggestions.textContent = `Match results for: ${cur_filename}`;
  }
  update_ui_for_suggestions();
});

// called whenever the 
// should only occur when 1) doing a match find. 2) rejecting 3) accepting.
// assumes at least one match.
function ui_load_current_match() {
  const match = current_match_suggestions.at(-1);
  const group_name = match[0];
  scroll_div_for_match_snippet.innerHTML = group_name_to_snippet.get(group_name);
  const func_name_list = Array.from(match[1].values());
  scroll_div_for_func_name_list.textContent = func_name_list.join('\n');
  match_snippets_label.textContent = `Matching Snippet | ${group_name}`;
}

function update_ui_for_suggestions() {
  if (uploaded_files.length === 0) {
    current_match_suggestions.length = 0;
  }
  find_matches_button.disabled = uploaded_files.length === 0;
  
  accept_match_button.disabled = reject_match_button.disabled = current_match_suggestions.length === 0;
  
  if (current_match_suggestions.length === 0) {
    // empty the suggestions div
    scroll_div_for_match_snippet.innerHTML = "";
    scroll_div_for_func_name_list.textContent = "";
    match_snippets_label.textContent = "Matching Snippet";
  } else {
    ui_load_current_match();
  }
}

accept_match_button.addEventListener("click", (event) => {
  const accepted_match = current_match_suggestions.pop();

  const name_of_current_match_group = accepted_match[0];
  add_filename_to_group(get_current_file().name, name_of_current_match_group);
  update_ui_for_suggestions();
  update_ui_for_group_membership();
});

reject_match_button.addEventListener("click", (event) => {
  current_match_suggestions.pop();
  update_ui_for_suggestions();
});


update_ui_for_current_file();
update_ui_for_current_group();
