package fr.n7.smt;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;

import com.microsoft.z3.*;

/**
 * Classe qui implémente l'algorithme de BMC pour la partie "chiffres"
 * du jeu "des chiffres et des lettres".
 */
public class Chiffres {

    /**
     * Contexte utilisé par l'instance Chiffres pour créer les formules,
     * solveurs, etc.
     */
    private Context context;

    /**
     * Cache de constantes booléennes, indicé par leur nom.
     */
    private HashMap<String, BoolExpr> boolCache = new HashMap<>();

    /**
     * Cache de constantes booléennes, indicé par leur nom.
     */
    private HashMap<String, BitVecExpr> bvCache = new HashMap<>();

    /**
     * Cache de constantes booléennes, indicé par leur nom.
     */
    private HashMap<String, IntExpr> intCache = new HashMap<>();

    /**
     * Cache de constantes booléennes, indicé par leur nom.
     */
    private HashMap<String, ArrayExpr> arrayCache = new HashMap<>();

    /**
     * Nombre de bits de la représentation des bitvectors.
     */
    private int bvBits;

    /**
     * Sorte bitvector de taille bvBits.
     */
    private Sort bvSort;

    /**
     * Sorte tableaux à indices intSort et elements bitvectors de
     * taille bvBits.
     */
    private Sort bvArraySort;

    /**
     * Sorte des entiers mathématiques.
     */
    private Sort intSort;

    /**
     * Constantes numériques pour le calcul du système de transition.
     */
    private int[] nums;

    /**
     * Valeur cible du calcul du système de transition.
     */
    private int target;

    /**
     * Nombre maximum d'étapes de calcul du système de transition.
     */
    private int maxNofSteps;

    /**
     * Si vrai alors interdiction d'overflow sur les operations bitvector.
     */
    private boolean noOverflows;
    private BigInteger maxBvRange;
    private BigInteger minBvRange;

    /**
     * Initialise tous les attributs de la classe: paramètres utilisateur,
     * contexte, sortes.
     */
    public Chiffres(int[] _nums, int _target, int _bvBits, boolean _noOverflows) {
        nums = _nums;
        target = _target;
        bvBits = _bvBits;
        maxBvRange = new BigInteger("2").pow(bvBits - 1).subtract(new BigInteger("1"));
        minBvRange = new BigInteger("2").pow(bvBits - 1).negate();
        maxNofSteps = 2 * nums.length - 1;
        noOverflows = _noOverflows;

        HashMap<String, String> cfg = new HashMap<>();
        cfg.put("model", "true");
        cfg.put("proof", "true");

        context = new Context(cfg);
        intSort = context.mkIntSort();
        bvSort = context.mkBitVecSort(bvBits);
        bvArraySort = context.mkArraySort(intSort, bvSort);
        boolCache = new HashMap<>();
        bvCache = new HashMap<>();
        intCache = new HashMap<>();
        arrayCache = new HashMap<>();
    }

    /**
     * Retourne la constante du cache si présente, ou bien en crée une
     * nouvelle avec le nom donné si absente.
     */
    private BoolExpr boolConst(String name) {
        BoolExpr res = boolCache.get(name);

        if (res == null) {
            res = context.mkBoolConst(name);
            boolCache.put(name, res);
        }

        return res;
    }

    /**
     * Retourne la constante du cache si présente, ou bien en crée une
     * nouvelle avec le nom donné si absente.
     */
    private BitVecExpr bvConst(String name) {
        BitVecExpr res = bvCache.get(name);

        if (res == null) {
            res = context.mkBVConst(name, bvBits);
            bvCache.put(name, res);
        }

        return res;
    }

    /**
     * Retourne la constante du cache si présente, ou bien en crée une
     * nouvelle avec le nom donné si absente.
     */
    private IntExpr intConst(String name) {
        IntExpr res = intCache.get(name);

        if (res == null) {
            res = context.mkIntConst(name);
            intCache.put(name, res);
        }

        return res;
    }

    /**
     * Retourne la constante du cache si présente, ou bien en crée une
     * nouvelle avec le nom donné si absente.
     */
    private ArrayExpr arrayConst(String name) {
        ArrayExpr res = arrayCache.get(name);

        if (res == null) {
            res = context.mkArrayConst(name, intSort, bvSort);
            arrayCache.put(name, res);
        }

        return res;
    }

    /**
     * Expression vraie ssi exactement une des exprs est vraie.
     */
    private BoolExpr exactlyOne(BoolExpr... exprs) {
        return context.mkAnd(context.mkOr(exprs), atMostOne(exprs));
    }

    /**
     * Expression vraie ssi au plus une des exprs est vraie.
     */
    private BoolExpr atMostOne(BoolExpr... exprs) {
        ArrayList<BoolExpr> conjuncts = new ArrayList<>();

        for (BoolExpr expr : exprs) {
            ArrayList<BoolExpr> otherExprs = new ArrayList<>();
            for (BoolExpr e : exprs) {
                if (e != expr) {
                    otherExprs.add(e);
                }
            }

            BoolExpr bigOr = context.mkOr(otherExprs.stream().toArray(BoolExpr[]::new));
            BoolExpr res = context.mkImplies(expr, context.mkNot(bigOr));

            conjuncts.add(res);
        }

        return context.mkAnd(conjuncts.stream().toArray(BoolExpr[]::new));
    }

    /**
     * Convertit un int java en valeur symbolique bitvector Z3.
     */
    private BitVecNum toBvNum(int num) {
        if (noOverflows) {
            BigInteger bigNum = new BigInteger(String.valueOf(num));

            if (bigNum.compareTo(minBvRange) >= 0 && bigNum.compareTo(maxBvRange) <= 0)
                return context.mkBV(num, bvBits);
            else
                throw new Error("le numeral " + String.valueOf(num) +
                        " dépasse la capacité des bitvectors signés de taille " +
                        String.valueOf(bvBits));
        } else {
            return context.mkBV(num, bvBits);
        }
    }

    /**
     * Trigger de l'action "pousser un numéral sur la pile" pour le pas
     * d'execution "step" du calcul.
     */
    private BoolExpr pushNumVar(int step, int num) {
        return boolConst("push_" + String.valueOf(num) + "@" +
                String.valueOf(step));
    }

    /**
     * Trigger de l'action "additionner les deux éléments du dessus de
     * pile et pousser le resultat en dessus de pile" pour le pas
     * d'execution "step" du calcul.
     */
    private BoolExpr addVar(int step) {
        return boolConst("add@" + String.valueOf(step));
    }

    /**
     * Trigger de l'action "soustraire les deux éléments du dessus de
     * pile et pousser le resultat en dessus de pile" pour le pas
     * d'execution "step" du calcul.
     */
    private BoolExpr subVar(int step) {
        return boolConst("sub@" + String.valueOf(step));
    }

    /**
     * Trigger de l'action "multiplier les deux éléments du dessus de
     * pile et pousser le resultat en dessus de pile" pour le pas
     * d'execution "step" du calcul.
     */
    private BoolExpr mulVar(int step) {
        return boolConst("mul@" + String.valueOf(step));
    }

    /**
     * Trigger de l'action "diviser les deux éléments du dessus de
     * pile et pousser le resultat en dessus de pile" pour le pas
     * d'execution "step" du calcul.
     */
    private BoolExpr divVar(int step) {
        return boolConst("div@" + String.valueOf(step));
    }

    /**
     * Variable d'état représentant la pile au pas d'exécution "step".
     */
    private ArrayExpr stackStateVar(int step) {
        return arrayConst("stack@" + String.valueOf(step));
    }

    /**
     * Variable d'état représentant l'indice de dessus de pile au pas
     * d'exécution "step".
     */
    private IntExpr idxStateVar(int step) {
        return intConst("idx@" + String.valueOf(step));
    }

    /**
     * Formule de transition, vraie ssi l'état au pas step et au pas
     * step + 1 sont liés par une action "push(num)".
     */
    private BoolExpr pushNumFormula(int step, int num) {
        ArrayExpr pile = stackStateVar(step);
        ArrayExpr pileSucc = stackStateVar(step + 1);

        IntExpr idxPile = idxStateVar(step);
        IntExpr idxPileSucc = idxStateVar(step + 1);

        BoolExpr valeurSucc = context.mkEq(pileSucc, context.mkStore(pile, idxPile, toBvNum(num)));
        BoolExpr stepSucc = context.mkEq(idxPileSucc, context.mkAdd(context.mkInt(1), idxPile));

        BoolExpr unicite = context.mkTrue();
        for (int i = 0; i < step; i++)
            unicite = context.mkAnd(unicite, context.mkNot(pushNumVar(i, num)));

        return context.mkImplies(pushNumVar(step, num) , context.mkAnd(valeurSucc, unicite, stepSucc));
    }


    private interface ActionVar {
        /**
         * Retourne la variable trigger de l'action au step donné.
         */
        BoolExpr get(int step);
    }

    private interface ActionResult {
        /**
         * Retourne l'expression du résultat de l'action au step donné
         * en fonction de e1 et e2, les deux valeurs du dessus de la pile.
         */
        BitVecExpr get(int step, BitVecExpr e1, BitVecExpr e2);
    }

    private interface ActionPrecondition {
        /**
         * Retourne l'expression de la précondition de l'action au step
         * donné en fonction de e1 et e2, les deux valeurs du dessus de
         * la pile.
         */
        BoolExpr get(int step, BitVecExpr e1, BitVecExpr e2);
    }


    private BoolExpr actionFormula(int step, ActionVar actVar, ActionPrecondition precond, ActionResult opRes) {
        ArrayExpr pile = stackStateVar(step);
        ArrayExpr pileSucc = stackStateVar(step + 1);

        IntExpr idxPile = idxStateVar(step);
        IntExpr idxPileSucc = idxStateVar(step + 1);

        BoolExpr stepSucc = context.mkEq(idxPileSucc, context.mkSub(idxPile, context.mkInt(1)));

        BitVecExpr right = (BitVecExpr) context.mkSelect(pile, context.mkSub(idxPile, context.mkInt(1)));
        BitVecExpr left = (BitVecExpr) context.mkSelect(pile, context.mkSub(idxPile, context.mkInt(2)));

        BoolExpr action = actVar.get(step);
        BoolExpr preCond = precond.get(step, left, right);
        BitVecExpr res = opRes.get(step, left, right);

        ArrayExpr pileSuccRes = context.mkStore(pile, context.mkSub(idxPile, context.mkInt(2)), res);
        BoolExpr coherenceRes = context.mkEq(pileSuccRes, pileSucc);

        BoolExpr actionPossible = context.mkGe(idxPile, context.mkInt(2));

        return context.mkImplies(context.mkAnd(preCond, action), context.mkAnd(actionPossible, coherenceRes, stepSucc));
    }

    /**
     * Formule de transition, vraie ssi l'état au pas step et au pas
     * step + 1 sont liés par une action "addition".
     */
    private BoolExpr addFormula(int step) {
        ActionVar add = this::addVar;
        ActionPrecondition precond = (s, e1, e2) -> context.mkTrue();
        ActionResult opRes = (s, e1, e2) -> context.mkBVAdd(e1, e2);

        return actionFormula(step, add, precond, opRes);
    }

    /**
     * Formule de transition, vraie ssi l'état au pas step et au pas
     * step + 1 sont liés par une action "soustraction".
     */
    private BoolExpr subFormula(int step) {
        ActionVar sub = this::subVar;
        ActionPrecondition precond = (s, e1, e2) -> context.mkTrue();
        ActionResult opRes = (s, e1, e2) -> context.mkBVSub(e1, e2);

        return actionFormula(step, sub, precond, opRes);
    }

    /**
     * Formule de transition, vraie ssi l'état au pas step et au pas
     * step + 1 sont liés par une action "multiplication".
     */
    private BoolExpr mulFormula(int step) {
        ActionVar mul = this::mulVar;
        ActionPrecondition precond = (s, e1, e2) -> context.mkTrue();
        ActionResult opRes = (s, e1, e2) -> context.mkBVMul(e1, e2);

        return actionFormula(step, mul, precond, opRes);
    }

    /**
     * Formule de transition, vraie ssi l'état au pas step et au pas
     * step + 1 sont liés par une action "division".
     */
    private BoolExpr divFormula(int step) {
        ActionVar div = this::divVar;
        ActionPrecondition precond = (s, e1, e2) -> context.mkTrue();
        ActionResult opRes = (s, e1, e2) -> context.mkBVSDiv(e1, e2);

        return actionFormula(step, div, precond, opRes);
    }

    /**
     * Tableau contenant tous les triggers d'actions push, mul,
     * div, add, sub au pas "step".
     */
    private BoolExpr[] allActions(int step) {
        ArrayList<BoolExpr> arr = new ArrayList<>();

        for (int num : nums) {
            arr.add(pushNumVar(step, num));
        }

        arr.add(mulVar(step));
        arr.add(divVar(step));
        arr.add(addVar(step));
        arr.add(subVar(step));

        return arr.stream().toArray(BoolExpr[]::new);
    }

    /**
     * Formule vraie ssi les états aux pas step et step+1 sont liés par
     * une transition d'action.
     */
    private BoolExpr transitionFormula(int step) {
        BoolExpr boolExpr = context.mkTrue();

        for (int num : nums) {
            boolExpr = context.mkAnd(boolExpr, pushNumFormula(step, num));
        }

        boolExpr = context.mkAnd(boolExpr, mulFormula(step));
        boolExpr = context.mkAnd(boolExpr, addFormula(step));
        boolExpr = context.mkAnd(boolExpr, subFormula(step));
        boolExpr = context.mkAnd(boolExpr, divFormula(step));

        return context.mkAnd(boolExpr, exactlyOne(allActions(step)));
    }

    /**
     * Formule vraie ssi la pile est dans son état initial (au pas 0,
     * toutes les cellules à zéro et dessus de pile à zero).
     */
    private BoolExpr initialStateFormula() {
        ArrayExpr pile = stackStateVar(0);
        IntExpr idxPile = idxStateVar(0);
        BoolExpr pileInit = context.mkEq(pile, context.mkConstArray(intSort, toBvNum(0)));
        BoolExpr idxInit = context.mkEq(idxPile, context.mkInt(0));
        return context.mkAnd(pileInit, idxInit);
    }

    /**
     * Formule vraie ssi la pile ne contient qu'un élément qui est égal
     * à la valeur cible au pas "step".
     */
    private BoolExpr finalStateFormula(int step) {
        ArrayExpr pile = stackStateVar(step);
        IntExpr idxPile = idxStateVar(step);
        BitVecExpr valeur = (BitVecExpr) context.mkSelect(pile, context.mkInt(0));
        BoolExpr valEqTarget = context.mkEq(valeur, toBvNum(target));
        BoolExpr idxEq1 = context.mkEq(idxPile, context.mkInt(1));
        return context.mkAnd(valEqTarget, idxEq1);
    }

    /**
     * Algorithme de résolution exacte. Déroule une boucle de
     * model-checking borné de la relation de transition depuis l'état
     * initial sur au plus maxNofSteps. Pour chaque itération de
     * model-checking, on ajoute une formule de transition pour le step
     * suivant dans le solveur, on pousse la formule d'état final, on
     * lance une résolution. Si le problème est SAT, on imprime la
     * solution, si le problème est UNSAT, on retire la formule d'état
     * final et on passe à l'itération suivante. Si le problème est
     * UNKNOWN, on retourne le status UNKOWN. Si le problème est UNSAT
     * pour toutes les itérations, on retourne le status UNSAT.
     */
    private Status solveExact(int timeout) {
        long startTime = System.currentTimeMillis();
        Solver solver = context.mkSolver();

        if (timeout > 0) {
            Params p = context.mkParams();
            p.add("timeout", timeout);
            solver.setParameters(p);
            System.out.println("\n\nsolveExact with timeout " + String.valueOf(timeout));
        } else {
            System.out.println("\n\nsolveExact without timeout");
        }

        // ETAPE 0
        Status status = Status.UNSATISFIABLE;
        int step = 0;

        solver.add(initialStateFormula());

        solver.push();
        solver.add(finalStateFormula(step));
        if (solver.check() == Status.SATISFIABLE) {
            status = Status.SATISFIABLE;
            System.out.println("PROBLEM is SAT");
            printModel(solver.getModel(), step);
        } else if (solver.check() == Status.UNKNOWN)
            status = Status.UNKNOWN;
        else
            solver.pop();

        // ETAPES 1..*
        while (status == Status.UNSATISFIABLE) {
            step++;
            solver.add(transitionFormula(step - 1));

            solver.push();
            solver.add(finalStateFormula(step));

            if (solver.check() == Status.SATISFIABLE) {
                status = Status.SATISFIABLE;
                System.out.println("PROBLEM is SAT");
                printModel(solver.getModel(), step);
            } else if (timeout > 0 && System.currentTimeMillis() - startTime >= timeout) {
                System.out.println("PROBLEM is UNSAT\nFlag : Timeout dépassé");
                break;
            } else if (step > maxNofSteps) {
                System.out.println("PROBLEM is UNSAT\nFlag : Nombre d'étapes trop grand");
                break;
            } else if (solver.check() == Status.UNKNOWN) {
                status = Status.UNKNOWN;
                System.out.println("PROBLEM is UNKNOWN");
                break;
            } else
                solver.pop();
            }
            return status;
    }

    /**
     * Formule vraie ssi la pile n'est pas dans son état final au pas
     * "step".
     */
    private BoolExpr finalStateApproxFormula(int step) {
        return context.mkNot(finalStateFormula(step));
    }

    /**
     * Critère d'optimisation, écart en valeur absolue entre la valeur
     * du dessus de la pile et la valeur cible au pas "step".
     */
    private BitVecExpr finalStateApproxCriterion(int step) {
        ArrayExpr pile = stackStateVar(step);
        BitVecExpr valeur = (BitVecExpr) context.mkSelect(pile, context.mkInt(0));
        if (context.mkBVSGE(valeur, toBvNum(target)).isTrue())
            return context.mkBVSub(valeur, toBvNum(target));
        else
            return context.mkBVSub(toBvNum(target), valeur);
    }

    Optimize constructOptimize(int timeout, int step) {
        Optimize solver = context.mkOptimize();
        solver.MkMinimize(finalStateApproxCriterion(step));
        if (timeout > 0) {
            Params p = context.mkParams();
            p.add("timeout", timeout);
            solver.setParameters(p);
        }
        return solver;
    }

    /**
     * Algorithme de résolution approchée par optimisation max-SMT. À
     * chaque étape de BMC, on minimise la distance à la cible. Le
     * solveur d'optimisation n'est pas incrémental donc push et pop ne
     * sont pas disponibles, on instancie donc un nouveau solveur et
     * toutes les contraintes jusqu'au pas "step" à chaque itération,
     * ainsi que le critère à optimiser. Pour chaque itération le
     * problème est sensé être SAT et on imprime la solution à chaque
     * itération. Si le problème est UNSAT, on retire la formule d'état
     * final et on passe à l'itération suivante. Si le problème est
     * UNKNOWN, on retourne le status UNKOWN. Si le problème était SAT
     * pour toutes les itérations, on retourne le status SAT.
     */
    private Status solveApprox(int timeout) {
        long startTime = System.currentTimeMillis();
        List<BoolExpr> mem = new ArrayList<>();
        int step = 0;

        Optimize solver = constructOptimize(timeout, step);
        if (timeout > 0) {
            System.out.println("\n\nsolveApprox with timeout " + String.valueOf(timeout));
        } else {
            System.out.println("\n\nsolveApprox without timeout");
        }

        // ETAPE 0
        Status status = Status.UNSATISFIABLE;

        solver.Add(initialStateFormula());
        mem.add(initialStateFormula());

        solver.Add(finalStateFormula(step));
        if (solver.Check() == Status.SATISFIABLE) {
            status = Status.SATISFIABLE;
            System.out.println("Step n°" + step);
            printModel(solver.getModel(), step);
        } else if (solver.Check() == Status.UNKNOWN)
            return Status.UNKNOWN;

        solver = constructOptimize(timeout, step);

        // ETAPE 1..*
        while (step < maxNofSteps) {
            step++;
            mem.add(transitionFormula(step - 1));

            for (BoolExpr b : mem)
                solver.Add(b);

            solver.Add(finalStateApproxFormula(step));

            if (solver.Check() == Status.SATISFIABLE) {
                status = Status.SATISFIABLE;
                System.out.println("\n|Step n°" + step + "|");
                printModel(solver.getModel(), step);
            } else if (timeout > 0 && System.currentTimeMillis() - startTime >= timeout) {
                System.out.println("Timeout dépassé");
                break;
            } else if (solver.Check() == Status.UNKNOWN) {
                status = Status.UNKNOWN;
                System.out.println("PROBLEM is UNKNOWN");
                break;
            }
            solver = constructOptimize(timeout, step);
        }
        return status;
    }

    /**
     * Résout le problème en essayant une résolution exacte,
     * puis une résolution approximative en cas d'échec.
     */
    Status solve(int timeout) {
        printParams();

        Status s = solveExact(timeout);

        if (s != Status.SATISFIABLE) {
            s = solveApprox(timeout);
        }

        return s;
    }

    /**
     * Affiche le contenu de la pile en ASCII sur sdtout.
     */
    private void printStackAtStep(Model m, int step) {
        for (int idx = 0; idx <= maxNofSteps; idx++) {
            BitVecExpr resbv =
                    (BitVecExpr) context.mkSelect(stackStateVar(step),
                            context.mkInt(idx));
            IntExpr resi = context.mkBV2Int(resbv, true);

            if (m.eval(context.mkEq(idxStateVar(step),
                    context.mkInt(idx)), true).isTrue()) {
                System.out.print(" <| ");
            } else {
                System.out.print(" | ");
            }

            System.out.print(m.eval(resi, true));
        }

        System.out.println();
    }

    /**
     * Affiche le contenu d'un modèle m obtenu par BMC jusqu'à
     * la profondeur steps.
     */
    private void printModel(Model m, int steps) {
        System.out.print("init ~> ");
        printStackAtStep(m, 0);

        for (int step = 0; step <= steps; step++) {
            for (int num : nums) {
                if (m.eval(pushNumVar(step, num), true).isTrue()) {
                    System.out.print("push " + String.valueOf(num) + " ~> ");
                }
            }

            if (m.eval(mulVar(step), true).isTrue()) {
                System.out.print("mul ~> ");
            }

            if (m.eval(divVar(step), true).isTrue()) {
                System.out.print("div ~> ");
            }

            if (m.eval(addVar(step), true).isTrue()) {
                System.out.print("add ~> ");
            }

            if (m.eval(subVar(step), true).isTrue()) {
                System.out.print("sub ~> ");
            }

            printStackAtStep(m, step + 1);
        }
    }

    private void printParams() {
        System.out.println("\nParameters:");
        System.out.println("- bvBits     :" + String.valueOf(bvBits));
        System.out.println("- noOverflows:" + String.valueOf(noOverflows));
        System.out.println("- nums       :" + Arrays.toString(nums));
        System.out.println("- target     :" + String.valueOf(target));
    }
}
