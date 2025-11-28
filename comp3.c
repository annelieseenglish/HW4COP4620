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

void print_edges_cfg(struct cfg* r){
  struct cfg* t = r;
  while (t != NULL){
    if (t->valid) fprintf(fp, "%d->%d\n", t->src, t->dst);
    t = t->next;
  }
}

void print_ir(struct cfg* r, char* fun){
  printf("function %s:\n", fun);
  int sz = get_max_id(r);
  for (int i = 0; i < sz; i++)
  {
    struct cfg* t = r;
    while (t != NULL){
      if (t->valid && strcmp(fun, t->fun) == 0 && t->src == i)
      {
        // printing basic block with ID "t->src"
        printf(" bb%d:\n", t->src);
         struct ast* node = find_ast_node(t->dst);
        
        // Print the instruction based on node type
        if (node->ntoken == CONST || node->ntoken == VARID) {
          // Simple assignment: v5 := 10  or  v2 := a1
          printf("  v%d := %s\n", node->id, node->token);
        }
        else if (is_op(node->ntoken)) {
          // Operation: v7 := v5 < v6
          printf("  v%d := ", node->id);
          int n = get_child_num(node);
          
          for (int j = 1; j <= n; j++) {
            printf("v%d", get_child(node, j)->id);
            if (j < n) printf(" %s ", node->token);
          }
          printf("\n");
        }
        else if (node->ntoken == CALL) {
          // Function call: call f
          printf("  call %s\n", node->token);
        }
        else if (node->ntoken == IF) {
          // For IF nodes, the assignment happens at the merge point
          // This is handled by the branch destinations
          // Print nothing here, or you can print a comment
        }
        
        // Print branch instruction
        // Find all edges from t->dst
        struct cfg* branch = r;
        int branch_count = 0;
        int branch_targets[2] = {-1, -1};
        
        while (branch != NULL) {
          if (branch->valid && 
              strcmp(fun, branch->fun) == 0 && 
              branch->src == t->dst && 
              branch_count < 2) {
            branch_targets[branch_count] = branch->dst;
            branch_count++;
          }
          branch = branch->next;
        }
        
        // Print the branch based on how many targets we found
        if (branch_count == 1) {
          // Unconditional branch
          printf("  br bb%d\n", branch_targets[0]);
        }
        else if (branch_count == 2) {
          // Conditional branch: br v7 bb8 bb11
          printf("  br v%d bb%d bb%d\n", t->dst, branch_targets[0], branch_targets[1]);
        }
        // If branch_count == 0, this is a final node (return), no branch
        
        break; //Next basic block
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

struct cfg* t = cfg_r;
while (t != NULL) {
  if (t->valid && t->fun != NULL) {
	int already_printed = 0;
	for (int i = 0; i < num_printed; i++) {
	   if (strcmp(printed_functions[i], t->fun) == 0) {
		already_printed = 1;
		break;
	}
     }
	if (!already_printed) {
	   print_ir(cfg_r, t->fun);
	   printf("\n");
	   printed_functions[num_printed++] = t->fun;
	   }
	}
		t = t->next;
	}
  free_ast();
  return retval;
}
