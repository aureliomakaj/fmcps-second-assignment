import pynusmv
import sys
from pynusmv.dd import BDD, State
from pynusmv.fsm import BddFsm
from pynusmv.prop import Spec
from pynusmv_lower_interface.nusmv.parser import parser 
from collections import deque

specTypes = {
    'LTLSPEC': parser.TOK_LTLSPEC, 
    'CONTEXT': parser.CONTEXT,
    'IMPLIES': parser.IMPLIES, 
    'IFF': parser.IFF, 
    'OR': parser.OR, 
    'XOR': parser.XOR, 
    'XNOR': parser.XNOR,
    'AND': parser.AND, 
    'NOT': parser.NOT, 
    'ATOM': parser.ATOM, 
    'NUMBER': parser.NUMBER, 
    'DOT': parser.DOT,

    'NEXT': parser.OP_NEXT, 
    'OP_GLOBAL': parser.OP_GLOBAL, 
    'OP_FUTURE': parser.OP_FUTURE,
    'UNTIL': parser.UNTIL,
    'EQUAL': parser.EQUAL, 
    'NOTEQUAL': parser.NOTEQUAL, 
    'LT': parser.LT, 
    'GT': parser.GT,
    'LE': parser.LE, 
    'GE': parser.GE, 
    'TRUE': parser.TRUEEXP, 
    'FALSE': parser.FALSEEXP
}

basicTypes = {
    parser.ATOM, 
    parser.NUMBER, 
    parser.TRUEEXP, 
    parser.FALSEEXP, 
    parser.DOT,
    parser.EQUAL, 
    parser.NOTEQUAL, 
    parser.LT, 
    parser.GT, 
    parser.LE, 
    parser.GE
}

booleanOp = {
    parser.AND, 
    parser.OR, 
    parser.XOR, 
    parser.XNOR, 
    parser.IMPLIES, 
    parser.IFF
}

def spec_to_bdd(model: BddFsm, spec: Spec) -> BDD:
    """
    Given a formula `spec` with no temporal operators, returns a BDD equivalent to
    the formula, that is, a BDD that contains all the states of `model` that
    satisfy `spec`
    """
    bddspec = pynusmv.mc.eval_simple_expression(model, str(spec))
    return bddspec
    
def is_boolean_formula(spec: Spec):
    """
    Given a formula `spec`, checks if the formula is a boolean combination of base
    formulas with no temporal operators. 
    """
    if spec.type in basicTypes:
        return True
    if spec.type == specTypes['NOT']:
        return is_boolean_formula(spec.car)
    if spec.type in booleanOp:
        return is_boolean_formula(spec.car) and is_boolean_formula(spec.cdr)
    return False
    
def check_GF_formula(spec: Spec):
    """
    Given a formula `spec` checks if the formula is of the form GF f, where f is a 
    boolean combination of base formulas with no temporal operators.
    Returns the formula f if `spec` is in the correct form, None otherwise 
    """
    # check if formula is of type GF f_i
    if spec.type != specTypes['OP_GLOBAL']:
        return False
    spec = spec.car
    if spec.type != specTypes['OP_FUTURE']:
        return False
    if is_boolean_formula(spec.car):
        return spec.car
    else:
        return None

def parse_react(spec: Spec):
    """
    Visit the syntactic tree of the formula `spec` to check if it is a reactive formula,
    that is wether the formula is of the form
    
                    GF f -> GF g
    
    where f and g are boolean combination of basic formulas.
    
    If `spec` is a reactive formula, the result is a pair where the first element is the 
    formula f and the second element is the formula g. If `spec` is not a reactive 
    formula, then the result is None.
    """
    # the root of a spec should be of type CONTEXT
    if spec.type != specTypes['CONTEXT']:
        return None
    # the right child of a context is the main formula
    spec = spec.cdr
    # the root of a reactive formula should be of type IMPLIES
    if spec.type != specTypes['IMPLIES']:
        return None
    # Check if lhs of the implication is a GF formula
    f_formula = check_GF_formula(spec.car)
    if f_formula == None:
        return None
    # Create the rhs of the implication is a GF formula
    g_formula = check_GF_formula(spec.cdr)
    if g_formula == None:
        return None
    return (f_formula, g_formula)

def check_react_spec(spec: Spec):
    """
    Return whether the loaded SMV model satisfies or not the GR(1) formula
    `spec`, that is, whether all executions of the model satisfies `spec`
    or not. 
    """
    (f_formula, g_formula) = parse_react(spec)
    print(f_formula, g_formula)
    if f_formula == None:
        return None
    fsm = get_model_bddFsm()
    """f_bdd = spec_to_bdd(fsm, f_formula)
    g_bdd = spec_to_bdd(fsm, g_formula)"""
    reach = compute_recheability(fsm)
    """print("reach")
    for s in fsm.pick_all_states(reach):
        print(s.get_str_values())
    print("---")"""
    f_liveness = check_liveness(fsm, reach, f_formula)
    tmp = pynusmv.mc.check_explain_ltl_spec(f_formula)
    print("F: ", f_liveness.is_true())
    print("F corretto: ", tmp[0])
    print(tmp[1])
    exit()
    g_liveness = check_liveness(fsm, reach, g_formula)
    print("G: ", g_liveness.is_true())
    res = f_liveness.imply(g_liveness)
    return (res.is_true(), pynusmv.mc.check_explain_ltl_spec(spec))
    if parse_react(spec) == None:
        return None
    return pynusmv.mc.check_explain_ltl_spec(spec)

def compute_recheability(fsm: BddFsm) -> BDD:
    reach = fsm.init
    new = fsm.init
    while new.isnot_false():
        new = fsm.post(new) - reach
        reach = reach + new
    return reach

def check_liveness(fsm: BddFsm, reach: BDD, spec: Spec) -> BDD:
    bdd_spec = spec_to_bdd(fsm, spec)
    recur = reach & (~bdd_spec)
    while recur.isnot_false():
        pre_reach = BDD.false()
        new = fsm.pre(recur)
        while new.isnot_false():
            pre_reach = pre_reach + new
            for s in fsm.pick_all_states(new):
                print(s.get_str_values())
            print("---")
            if recur.entailed(pre_reach):
                return BDD.false()
            new = fsm.pre(new) - pre_reach
        print("aaa -----")
        recur = recur & pre_reach
    return BDD.true()

def get_model_bddFsm() -> BddFsm :
    """
    Get the BDD-encoded finite-state machine representing the SMV model
    """
    return pynusmv.glob.prop_database().master.bddFsm

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "filename.smv")
        sys.exit(1)

    pynusmv.init.init_nusmv()
    filename = sys.argv[1]
    pynusmv.glob.load_from_file(filename)
    pynusmv.glob.compute_model()
    type_ltl = pynusmv.prop.propTypes['LTL']
    for prop in pynusmv.glob.prop_database():
        spec = prop.expr
        print(spec)
        if prop.type != type_ltl:
            print("property is not LTLSPEC, skipping")
            continue
        res = check_react_spec(spec)
        if res == None:
            print('Property is not a GR(1) formula, skipping')

        print("Mio res: ", res[0])
        print("Altro res: ", res[1][0])
        """if res[0] == True:
            print("Property is respected")
        elif res[0] == False:
            print("Property is not respected")
            print("Counterexample:", res[1])"""

    pynusmv.init.deinit_nusmv()
