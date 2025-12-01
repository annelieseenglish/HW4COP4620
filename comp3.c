#include "y.tab.h"
#include "ast.h"
#include "cfg.h"
int yyparse();


// symbol table
struct node_fun_str* fun_r = NULL;
struct node_fun_str* fun_t = NULL;
struct node_var_str* vars_r = NULL;
struct node_var_str* vars_t = NULL;

// cfg structure
struct cfg* cfg_r = NULL;
struct cfg* cfg_t = NULL;

static FILE *fp;

int to_cfg(struct ast* node)
{
  if (node->ntoken == FUNID) {
    struct ast *parent = node->parent;
    int how_many_children = get_child_num(parent);
    int id_fun_body = get_child(parent, how_many_children)->id;
    int interm = node->id;
    push_ncfg(interm, id_fun_body, true, false, node->token, &cfg_r, &cfg_t);
  }
  return 0;
}

bool is_op(int n)
{
  return (n == PLUS || n == MINUS || n == MULT ||
          n == EQ || n == GT || n == GE || n == LT || n == LE);
}

bool is_const_var(int n)
{
  return (n == CONST || n == VARID || n == CALL);
}

// Get number of parameters for a function by searching AST
int get_function_param_count(char* fun_name) {
  struct ast* node = find_ast_node(1); // Start from root
  struct ast* current = node;
  
  // Traverse all nodes
  for (int i = 1; i <= get_ast_size(); i++) {
    current = find_ast_node(i);
    if (current && current->ntoken == FUNID && strcmp(current->token, fun_name) == 0) {
      struct ast* parent = current->parent;
      if (parent && parent->ntoken == DEFFUN) {
        // Count INP children
        int count = 0;
        int num_children = get_child_num(parent);
        for (int j = 1; j <= num_children; j++) {
          struct ast* child = get_child(parent, j);
          if (child && child->ntoken == INP) {
            count++;
          }
        }
        return count;
      }
    }
  }
  return 0;
}

// Get parameter names for a function
void get_function_param_names(char* fun_name, char** param_names) {
  struct ast* current;
  for (int i = 1; i <= get_ast_size(); i++) {
    current = find_ast_node(i);
    if (current && current->ntoken == FUNID && strcmp(current->token, fun_name) == 0) {
      struct ast* parent = current->parent;
      if (parent && parent->ntoken == DEFFUN) {
        int idx = 0;
        int num_children = get_child_num(parent);
        for (int j = 1; j <= num_children; j++) {
          struct ast* child = get_child(parent, j);
          if (child && child->ntoken == INP) {
            param_names[idx++] = child->token;
          }
        }
        return;
      }
    }
  }
}

// Convert operator token to symbol
char* get_op_symbol(char* token) {
  if (strcmp(token, "PLUS") == 0) return "+";
  if (strcmp(token, "MINUS") == 0) return "-";
  if (strcmp(token, "MULT") == 0) return "*";
  if (strcmp(token, "LT") == 0) return "<";
  if (strcmp(token, "GT") == 0) return ">";
  if (strcmp(token, "LE") == 0) return "<=";
  if (strcmp(token, "GE") == 0) return ">=";
  if (strcmp(token, "EQ") == 0) return "==";
  return token;
}

int print_nodes(struct ast* node)
{
  if (node->ntoken == IF || is_op(node->ntoken) ||
      is_const_var(node->ntoken) || node->ntoken == FUNID) {
    fprintf(fp, "%d [label=\"%s\"];\n", node->id, node->token);
  }
  return 0;
}

int print_nodes_cfg(struct ast* node)
{
  if (node->ntoken == CONST || node->ntoken == VARID) {
    fprintf(fp, "%d [label=\"v%d := %s\"];\n", node->id, node->id, node->token);
  }
  if (node->ntoken == FUNID) {
    fprintf(fp, "%d [label=\"%s\"];\n", node->id, node->token);
  }
  if (node->ntoken == IF) {
    fprintf(fp, "%d [label=\"IF v%d = true, then v%d := v%d, else v%d := v%d\"];\n",
           node->id, get_child(node, 1)->id,
           node->id, get_child(node, 2)->id, node->id,
           get_child(node, 3)->id);
  }
  if (is_op(node->ntoken))
  {
    fprintf(fp, "%d [label=\"v%d := ", node->id, node->id);
    int n = get_child_num(node);
    if (n == 1) fprintf(fp, " NOT ");
    for (int i = 1; i <= n; i++) {
      fprintf(fp, "v%d", get_child(node, i)->id);
      if (i < n) fprintf(fp, " %s ", node->token);
      else fprintf(fp, "\"];\n");
    }
  }
  if (node->ntoken == CALL)
  {
    fprintf(fp, "%d [label=\"v%d := %s (", node->id, node->id, node->token);
    int n = get_child_num(node);
    for (int i = 1; i <= n; i++) {
      fprintf(fp, "v%d", get_child(node, i)->id);
      if (i < n) fprintf(fp, ", ");
    }
    fprintf(fp, ")\"];\n");
  }
  return 0;
}

void to_cfg_iter()
{
  struct cfg* r = cfg_r;
  while (r != NULL){
    if (r->valid && !r->final) {
      struct ast *node = find_ast_node(r->dst);
      if (!node->is_leaf){
        r->valid = false;
        int interm = r->src;

        if (node->ntoken == IF)
        {
          int cur = get_child(node, 1)->id;
          push_ncfg(interm, cur, true, false, r->fun, &cfg_r, &cfg_t);
          push_cfg(cur, get_child(node, 2)->id, true, false, &cfg_r, &cfg_t);
          push_cfg(cur, get_child(node, 3)->id, true, false, &cfg_r, &cfg_t);
          push_cfg(get_child(node, 2)->id, r->dst, true, true, &cfg_r, &cfg_t);
          push_cfg(get_child(node, 3)->id, r->dst, true, true, &cfg_r, &cfg_t);
        }
        else if (is_op(node->ntoken) || node->ntoken == CALL)
        {
          for (int i = 1; i <= get_child_num(node); i++) {
            int cur = get_child(node, i)->id;
            push_ncfg(interm, cur, true, false, r->fun, &cfg_r, &cfg_t);
            interm = cur;
          }
          push_ncfg(interm, r->dst, true, true, r->fun, &cfg_r, &cfg_t);
        }
      }
    }
    r = r->next;
  }
}

// IR instruction types
typedef enum {
  IR_ASSIGN,      // v1 := v2  or  v1 := 5
  IR_BINOP,       // v1 := v2 + v3
  IR_CALL,        // call f
  IR_BRANCH,      // br bb5
  IR_CBRANCH,     // br v1 bb2 bb3
  IR_PARAM_READ,  // v1 := a1
  IR_PARAM_WRITE, // a1 := v2
  IR_RV_READ,     // v1 := rv
  IR_RV_WRITE     // rv := v1
} IRInstrType;

typedef struct ir_instr {
  IRInstrType type;
  int dest_vreg;        // Destination virtual register
  int src_vreg1;        // Source vreg 1
  int src_vreg2;        // Source vreg 2
  char* op;             // Operator for BINOP
  char* func_name;      // Function name for CALL
  int constant_val;     // For constant assignments
  char* constant_str;   // For constant string
  int is_constant;      // Flag for constant
  int branch_target1;   // Branch target BB
  int branch_target2;   // Second branch target for conditional
  int cond_vreg;        // Condition vreg for conditional branch
  struct ir_instr* next;
} IRInstr;

typedef struct ir_block {
  int bb_num;
  IRInstr* instrs;      // Linked list of instructions
  IRInstr* last_instr;  // For easy appending
  struct ir_block* next;
} IRBlock;

typedef struct ir_function {
  char* name;
  int num_params;
  char** param_names;
  IRBlock* blocks;
  IRBlock* last_block;
  int next_bb;
  int next_vreg;
} IRFunction;

// Helper to create new IR instruction
IRInstr* new_ir_instr(IRInstrType type) {
  IRInstr* instr = (IRInstr*)malloc(sizeof(IRInstr));
  instr->type = type;
  instr->dest_vreg = -1;
  instr->src_vreg1 = -1;
  instr->src_vreg2 = -1;
  instr->op = NULL;
  instr->func_name = NULL;
  instr->constant_str = NULL;
  instr->is_constant = 0;
  instr->branch_target1 = -1;
  instr->branch_target2 = -1;
  instr->cond_vreg = -1;
  instr->next = NULL;
  return instr;
}

// Helper to create new basic block
IRBlock* new_ir_block(int bb_num) {
  IRBlock* block = (IRBlock*)malloc(sizeof(IRBlock));
  block->bb_num = bb_num;
  block->instrs = NULL;
  block->last_instr = NULL;
  block->next = NULL;
  return block;
}

// Add instruction to block
void add_instr_to_block(IRBlock* block, IRInstr* instr) {
  if (block->instrs == NULL) {
    block->instrs = instr;
    block->last_instr = instr;
  } else {
    block->last_instr->next = instr;
    block->last_instr = instr;
  }
}

// Create new basic block and add to function
IRBlock* add_block_to_func(IRFunction* func) {
  IRBlock* block = new_ir_block(func->next_bb);
  func->next_bb++;
  
  if (func->blocks == NULL) {
    func->blocks = block;
    func->last_block = block;
  } else {
    func->last_block->next = block;
    func->last_block = block;
  }
  
  return block;
}

// Generate IR for an expression (returns vreg holding result)
int generate_expr_ir(struct ast* expr, IRFunction* func, IRBlock** current_block) {
  
  if (expr->ntoken == CONST) {
    // Constant value
    IRBlock* const_block = add_block_to_func(func);
    IRInstr* instr = new_ir_instr(IR_ASSIGN);
    instr->dest_vreg = func->next_vreg++;
    instr->is_constant = 1;
    instr->constant_str = expr->token;
    add_instr_to_block(const_block, instr);

    IRInstr* branch = new_ir_instr(IR_BRANCH);
    branch->branch_target1 = func->next_bb;
    add_instr_to_block(const_block, branch);

    *current_block = const_block;
    return instr->dest_vreg;
  }
  
  else if (expr->ntoken == VARID) {
    // Variable reference
    IRBlock* var_block = add_block_to_func(func);
    IRInstr* instr = new_ir_instr(IR_ASSIGN);
    instr->dest_vreg = func->next_vreg++;
    
    // Check if this is a parameter
    int param_vreg = -1;
    for (int i = 0; i < func->num_params; i++) {
      if (strcmp(expr->token, func->param_names[i]) == 0) {
        param_vreg = i + 1; // Parameters are v1, v2, ...
        break;
      }
    }
    
    if (param_vreg != -1) {
      instr->src_vreg1 = param_vreg;
    } else {
      // Unknown variable - shouldn't happen in well-formed programs
      instr->is_constant = 1;
      instr->constant_str = expr->token;
    }
    
    add_instr_to_block(var_block, instr);

    IRInstr* branch = new_ir_instr(IR_BRANCH);
    branch->branch_target1 = func->next_bb;
    add_instr_to_block(var_block, branch);

    *current_block = var_block;
    return instr->dest_vreg;
  }
  
  else if (is_op(expr->ntoken)) {
    // Binary operation
    int num_operands = get_child_num(expr);
    
    // Generate IR for left operand
    IRBlock* left_block = NULL;
    int left_vreg = generate_expr_ir(get_child(expr, 1), func, &left_block);
    
    // Generate IR for right operand
    IRBlock* right_block = NULL;
    int right_vreg = generate_expr_ir(get_child(expr, 2), func, &right_block);
    
    // Create block for the operation
    IRBlock* op_block = add_block_to_func(func);
    IRInstr* instr = new_ir_instr(IR_BINOP);
    instr->dest_vreg = func->next_vreg++;
    instr->src_vreg1 = left_vreg;
    instr->src_vreg2 = right_vreg;
    instr->op = get_op_symbol(expr->token);
    add_instr_to_block(op_block, instr);

    IRInstr* branch = new_ir_instr(IR_BRANCH);
    branch->branch_target1 = func->next_bb;
    add_instr_to_block(op_block, branch);

    *current_block = op_block;
    return instr->dest_vreg;
  }
  

else if (expr->ntoken == IF) {
    // If expression: (if cond then_expr else_expr)
    struct ast* cond_expr = get_child(expr, 1);
    struct ast* then_expr = get_child(expr, 2);
    struct ast* else_expr = get_child(expr, 3);
    
    // Generate condition
    IRBlock* cond_block = NULL;
    int cond_vreg = generate_expr_ir(cond_expr, func, &cond_block);
    
    // Remove the auto-added branch from cond block (we'll add conditional branch)
    if (cond_block->last_instr && cond_block->last_instr->type == IR_BRANCH) {
      // Remove last instruction
      IRInstr* temp = cond_block->instrs;
      if (temp == cond_block->last_instr) {
        cond_block->instrs = NULL;
        cond_block->last_instr = NULL;
      } else {
        while (temp->next != cond_block->last_instr) {
          temp = temp->next;
        }
        temp->next = NULL;
        cond_block->last_instr = temp;
      }
    }
    
    // Remember BB numbers for branches
    int then_bb = func->next_bb;
    
    // Generate then branch
    IRBlock* then_block = NULL;
    int then_vreg = generate_expr_ir(then_expr, func, &then_block);
    
    // Remember BB after then branch
    int else_bb = func->next_bb;
    
    // Generate else branch
    IRBlock* else_block = NULL;
    int else_vreg = generate_expr_ir(else_expr, func, &else_block);
    
    // Add conditional branch to condition block
    IRInstr* cbranch = new_ir_instr(IR_CBRANCH);
    cbranch->cond_vreg = cond_vreg;
    cbranch->branch_target1 = then_bb;
    cbranch->branch_target2 = else_bb;
    add_instr_to_block(cond_block, cbranch);
    
    // Create join block
    int join_bb = func->next_bb;
    IRBlock* join_block = add_block_to_func(func);
    
    // Update last branches of then/else to point to join
    if (then_block->last_instr && then_block->last_instr->type == IR_BRANCH) {
      then_block->last_instr->branch_target1 = join_bb;
    }
    if (else_block->last_instr && else_block->last_instr->type == IR_BRANCH) {
      else_block->last_instr->branch_target1 = join_bb;
    }
    
    // In join block, create phi-like assignment
    // For now, we'll just pick one (proper SSA would need phi node)
    int result_vreg = func->next_vreg++;
    
    // Create two assignment instructions (one for each path)
    // In proper IR, we'd need to track which path we came from
    // For now, this is a simplification
    IRInstr* join_assign = new_ir_instr(IR_ASSIGN);
    join_assign->dest_vreg = result_vreg;
    join_assign->src_vreg1 = then_vreg;  // This should be phi(then_vreg, else_vreg)
    add_instr_to_block(join_block, join_assign);
    
    // Branch to next
    IRInstr* branch = new_ir_instr(IR_BRANCH);
    branch->branch_target1 = func->next_bb;
    add_instr_to_block(join_block, branch);
    
    *current_block = join_block;
    return result_vreg;
  }
 
  else if (expr->ntoken == CALL) {
    // Function call
    char* callee = expr->token;
    int num_args = get_child_num(expr);
    
    // Generate IR for each argument
    int arg_vregs[10];
    for (int i = 0; i < num_args; i++) {
      IRBlock* arg_block = NULL;
      arg_vregs[i] = generate_expr_ir(get_child(expr, i + 1), func, &arg_block);
    }
    
    // Create blocks for setting up arguments
    for (int i = 0; i < num_args; i++) {
      IRBlock* param_block = add_block_to_func(func);
      IRInstr* param_instr = new_ir_instr(IR_PARAM_WRITE);
      param_instr->dest_vreg = i + 1; // a1, a2, ...
      param_instr->src_vreg1 = arg_vregs[i];
      add_instr_to_block(param_block, param_instr);

     IRInstr* br = new_ir_instr(IR_BRANCH);
      br->branch_target1 = func->next_bb;
      add_instr_to_block(param_block, br);
    }
    
    // Create call block
    IRBlock* call_block = add_block_to_func(func);
    IRInstr* call_instr = new_ir_instr(IR_CALL);
    call_instr->func_name = callee;
    add_instr_to_block(call_block, call_instr);
    
    IRInstr* call_br = new_ir_instr(IR_BRANCH);
    call_br->branch_target1 = func->next_bb;
    add_instr_to_block(call_block, call_br);

    // Create block for reading return value
    IRBlock* rv_block = add_block_to_func(func);
    IRInstr* rv_instr = new_ir_instr(IR_RV_READ);
    rv_instr->dest_vreg = func->next_vreg++;
    add_instr_to_block(rv_block, rv_instr);

    IRInstr* branch = new_ir_instr(IR_BRANCH);
    branch->branch_target1 = func->next_bb;
    add_instr_to_block(rv_block, branch);

    *current_block = rv_block;
    return rv_instr->dest_vreg;
  }
  
  return -1;
}

// Generate IR for entire function
IRFunction* generate_function_ir(char* fun_name) {
  // Find function definition in AST
  struct ast* func_def = NULL;
  for (int i = 1; i <= get_ast_size(); i++) {
    struct ast* node = find_ast_node(i);
    if (node && node->ntoken == FUNID && strcmp(node->token, fun_name) == 0) {
      func_def = node->parent;
      break;
    }
  }
  
  if (!func_def || func_def->ntoken != DEFFUN) {
    return NULL;
  }
  
  // Create IR function structure
  IRFunction* ir_func = (IRFunction*)malloc(sizeof(IRFunction));
  ir_func->name = fun_name;
  ir_func->blocks = NULL;
  ir_func->last_block = NULL;
  ir_func->next_bb = 1;
  ir_func->next_vreg = 1;
  
  // Get parameters
  int num_children = get_child_num(func_def);
  ir_func->param_names = (char**)malloc(10 * sizeof(char*));
  ir_func->num_params = 0;
  
  for (int i = 1; i <= num_children; i++) {
    struct ast* child = get_child(func_def, i);
    if (child && child->ntoken == INP) {
      ir_func->param_names[ir_func->num_params++] = child->token;
    }
  }
  
  // Reserve v1, v2, ... for parameters
  ir_func->next_vreg = ir_func->num_params + 1;
  
  // Generate entry blocks for parameters
  for (int i = 0; i < ir_func->num_params; i++) {
    IRBlock* param_block = add_block_to_func(ir_func);
    IRInstr* instr = new_ir_instr(IR_PARAM_READ);
    instr->dest_vreg = i + 1;
    instr->src_vreg1 = i + 1; // Read from a1, a2, ...
    add_instr_to_block(param_block, instr);
    
    // Add branch to next block
    if (i < ir_func->num_params - 1) {
      IRInstr* branch = new_ir_instr(IR_BRANCH);
      branch->branch_target1 = ir_func->next_bb;
      add_instr_to_block(param_block, branch);
    }
  }
  
  // Get function body (last child)
  struct ast* body = get_child(func_def, num_children);
  
  // Generate IR for body
  IRBlock* body_end_block = NULL;
  int result_vreg = generate_expr_ir(body, ir_func, &body_end_block);
  
  // Add final block with rv assignment
  IRBlock* exit_block = body_end_block;
  IRInstr* rv_instr = new_ir_instr(IR_RV_WRITE);
  rv_instr->src_vreg1 = result_vreg;
  add_instr_to_block(exit_block, rv_instr);
  
  return ir_func;
}

// Print IR function
void print_ir_function(IRFunction* func) {
  if (!func) return;
  
  printf("function %s\n", func->name);
  
  IRBlock* block = func->blocks;
  while (block != NULL) {
    printf("bb%d:\n", block->bb_num);
    
    IRInstr* instr = block->instrs;
    while (instr != NULL) {
      switch (instr->type) {
        case IR_PARAM_READ:
          printf("  v%d := a%d\n", instr->dest_vreg, instr->src_vreg1);
          break;
          
        case IR_PARAM_WRITE:
          printf("  a%d := v%d\n", instr->dest_vreg, instr->src_vreg1);
          break;
          
        case IR_ASSIGN:
          if (instr->is_constant) {
            printf("  v%d := %s\n", instr->dest_vreg, instr->constant_str);
          } else {
            printf("  v%d := v%d\n", instr->dest_vreg, instr->src_vreg1);
          }
          break;
          
        case IR_BINOP:
          printf("  v%d := v%d %s v%d\n", instr->dest_vreg, 
                 instr->src_vreg1, instr->op, instr->src_vreg2);
          break;
          
        case IR_CALL:
          printf("  call %s\n", instr->func_name);
          break;
          
        case IR_RV_READ:
          printf("  v%d := rv\n", instr->dest_vreg);
          break;
          
        case IR_RV_WRITE:
          printf("  rv := v%d\n", instr->src_vreg1);
          break;
          
        case IR_BRANCH:
          printf("  br bb%d\n", instr->branch_target1);
          break;
          
        case IR_CBRANCH:
          printf("  br v%d bb%d bb%d\n", instr->cond_vreg,
                 instr->branch_target1, instr->branch_target2);
          break;
      }
      
      instr = instr->next;
    }
    
    block = block->next;
  }
}

/////
void print_ir(struct cfg* r, char* fun) {
  printf("function %s\n", fun);
  
  // Step 1: Get function info from AST
  int num_params = get_function_param_count(fun);
  char* param_names[10];
  get_function_param_names(fun, param_names);
  
  // Create mapping from parameter names to virtual registers
  int param_to_vreg[10];
  for (int i = 0; i < num_params; i++) {
    param_to_vreg[i] = i + 1; // v1, v2, etc.
  }
  
  // Step 2: Generate entry blocks
  int bb_counter = 1;
  
  if (strcmp(fun, "main") != 0) {
    for (int i = 0; i < num_params; i++) {
      printf("bb%d:\n", bb_counter);
      printf("  v%d := a%d\n", i + 1, i + 1);
      printf("  br bb%d\n", bb_counter + 1);
      bb_counter++;
    }
  }
  
  // Step 3: Find all CFG nodes for this function and renumber them
  int sz = get_max_id(r);
  int min_cfg_bb = 999999;
  
  // Find minimum BB number in CFG for this function
  struct cfg* t = r;
  while (t != NULL) {
    if (t->valid && strcmp(fun, t->fun) == 0) {
      if (t->src < min_cfg_bb) min_cfg_bb = t->src;
    }
    t = t->next;
  }
  
  // Create mapping from old BB numbers to new BB numbers
  int bb_map[1000];
  for (int i = 0; i < 1000; i++) bb_map[i] = -1;
  
  // Assign new BB numbers
  for (int i = min_cfg_bb; i <= sz; i++) {
    t = r;
    while (t != NULL) {
      if (t->valid && strcmp(fun, t->fun) == 0 && t->src == i) {
        bb_map[i] = bb_counter;
        bb_counter++;
        break;
      }
      t = t->next;
    }
  }
  
  // Step 4: Print all blocks with new numbering
  int final_vreg = -1;
  
  for (int original_bb = min_cfg_bb; original_bb <= sz; original_bb++) {
    if (bb_map[original_bb] == -1) continue;
    
    t = r;
    while (t != NULL) {
      if (t->valid && strcmp(fun, t->fun) == 0 && t->src == original_bb) {
        
        printf("bb%d:\n", bb_map[original_bb]);
        
        struct ast* node = find_ast_node(t->dst);
        
        // Print the instruction
        if (node->ntoken == CONST) {
          printf("  v%d := %s\n", node->id, node->token);
          final_vreg = node->id;
        }
        else if (node->ntoken == VARID) {
          // Map parameter names to their vregs
          int mapped = 0;
          for (int p = 0; p < num_params; p++) {
            if (strcmp(node->token, param_names[p]) == 0) {
              printf("  v%d := v%d\n", node->id, param_to_vreg[p]);
              mapped = 1;
              break;
            }
          }
          if (!mapped) {
            printf("  v%d := %s\n", node->id, node->token);
          }
          final_vreg = node->id;
        }
        else if (is_op(node->ntoken)) {
          printf("  v%d := ", node->id);
          int n = get_child_num(node);
          for (int j = 1; j <= n; j++) {
            printf("v%d", get_child(node, j)->id);
            if (j < n) printf(" %s ", get_op_symbol(node->token));
          }
          printf("\n");
          final_vreg = node->id;
        }
        else if (node->ntoken == CALL) {
          // Get call arguments
          int num_args = get_child_num(node);
          
          // Print argument setup blocks
          for (int arg = 0; arg < num_args; arg++) {
            struct ast* arg_node = get_child(node, arg + 1);
            printf("  a%d := v%d\n", arg + 1, arg_node->id);
            printf("  br bb%d\n", bb_map[original_bb] + arg + 1);
            printf("bb%d:\n", bb_map[original_bb] + arg + 1);
          }
          
          // Print call
          printf("  call %s\n", node->token);
          final_vreg = node->id;
        }
        else if (node->ntoken == IF) {
          // IF nodes don't print instructions, just handle branching
        }
        
        // Print branch instruction
        struct cfg* branch = r;
        int branch_count = 0;
        int branch_targets[2] = {-1, -1};
        
        while (branch != NULL) {
          if (branch->valid && strcmp(fun, branch->fun) == 0 && 
              branch->src == t->dst && branch_count < 2) {
            branch_targets[branch_count++] = branch->dst;
          }
          branch = branch->next;
        }
        
        if (node->ntoken == CALL && branch_count > 0) {
          // After call, read rv
          int next_bb = bb_map[original_bb] + num_params + 1; // Approximate
          printf("  br bb%d\n", next_bb);
          printf("bb%d:\n", next_bb);
          printf("  v%d := rv\n", node->id);
          if (bb_map[branch_targets[0]] != -1) {
            printf("  br bb%d\n", bb_map[branch_targets[0]]);
          }
        }
        else if (branch_count == 1) {
          if (bb_map[branch_targets[0]] != -1) {
            printf("  br bb%d\n", bb_map[branch_targets[0]]);
          }
        }
        else if (branch_count == 2) {
          if (bb_map[branch_targets[0]] != -1 && bb_map[branch_targets[1]] != -1) {
            printf("  br v%d bb%d bb%d\n", t->dst, 
                   bb_map[branch_targets[0]], bb_map[branch_targets[1]]);
          }
        }
        else if (branch_count == 0 && strcmp(fun, "main") != 0) {
          // Final block - assign to rv
          printf("  rv := v%d\n", t->dst);
        }
        
        break;
      }
      t = t->next;
    }
  }
}




int main (int argc, char **argv) {
  int retval = yyparse();

  // integrate your symbol table and semantic checks here
  
  print_ast();
  visit_ast(to_cfg);
  to_cfg_iter();

void print_edges_cfg(struct cfg* r){
  struct cfg* t = r;
  while (t != NULL){
    if (t->valid) fprintf(fp, "%d->%d\n", t->src, t->dst);
    t = t->next;
  }
}
  fp = fopen("cfg.dot", "w");
  fprintf(fp, "digraph print {\n");
  visit_ast(print_nodes_cfg);
  struct cfg* tmp = cfg_r;
  print_edges_cfg(cfg_r);
  fprintf(fp, "}\n");


  fclose(fp);
  system("dot -Tpdf cfg.dot -o cfg.pdf");

// Print IR for all functions found in CFG
char* printed_functions[100];	//tracking printed functions
int num_printed = 0;

char* functions[] = {"f", "g", "main"};
for (int i = 0; i < 3; i++) {
  IRFunction* ir_func = generate_function_ir(functions[i]);
  if (ir_func) {
    print_ir_function(ir_func);
    printf("\n");
  }
}

  free_ast();
  return retval;
}
