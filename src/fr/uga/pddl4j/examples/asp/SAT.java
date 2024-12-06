package fr.uga.pddl4j.examples.asp;

import fr.uga.pddl4j.heuristics.state.StateHeuristic;
import fr.uga.pddl4j.parser.DefaultParsedProblem;
import fr.uga.pddl4j.parser.RequireKey;
import fr.uga.pddl4j.plan.Plan;
import fr.uga.pddl4j.plan.SequentialPlan;
import fr.uga.pddl4j.planners.AbstractPlanner;
import fr.uga.pddl4j.planners.SearchStrategy;
import fr.uga.pddl4j.planners.statespace.search.StateSpaceSearch;
import fr.uga.pddl4j.problem.DefaultProblem;
import fr.uga.pddl4j.problem.Fluent;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Condition;
import fr.uga.pddl4j.problem.operator.Effect;
import fr.uga.pddl4j.problem.operator.ConditionalEffect;
import fr.uga.pddl4j.util.BitVector;
import fr.uga.pddl4j.problem.State;
import fr.uga.pddl4j.problem.operator.Action;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.TimeoutException;
import org.sat4j.core.VecInt;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import picocli.CommandLine;

@CommandLine.Command(name = "SAT", version = "SAT 1.0", description = "Solves a specified planning problem using SAT encoding search strategy.", sortOptions = false, mixinStandardHelpOptions = true, headerHeading = "Usage:%n", synopsisHeading = "%n", descriptionHeading = "%nDescription:%n%n", parameterListHeading = "%nParameters:%n", optionListHeading = "%nOptions:%n")

public class SAT extends AbstractPlanner {

    private double heuristicWeight;
    private StateHeuristic.Name heuristic;
    private final Map<Action, Integer> actionIds = new HashMap<>();
    private int nextActionId = 1; 

    private static final Logger LOGGER = LogManager.getLogger(SAT.class.getName());

    /**
     * Instantiates the planning problem from a parsed problem.
     *
     * @param problem the problem to instantiate.
     * @return the instantiated planning problem or null if the problem cannot be
     *         instantiated.
     */
    @Override
    public Problem instantiate(DefaultParsedProblem problem) {
        final Problem pb = new DefaultProblem(problem);
        pb.instantiate();
        return pb;
    }

    private int getActionId(Action action) {
        return actionIds.computeIfAbsent(action, a -> nextActionId++);
    }

    @Override
    public Plan solve(final Problem problem) {
        int actions = problem.getActions().size();
        int fluents = problem.getFluents().size();

        LOGGER.info("* Starting SAT-based search \n");

        ISolver solver = SolverFactory.newDefault();
        solver.newVar(actions * fluents); 
        solver.setTimeout(60);

        try {
            encodeInitialState(problem, solver);
            encodeGoalState(problem, solver);
            encodeActions(problem, solver);

            if (solver.isSatisfiable()) {
                LOGGER.info("* SAT search succeeded\n");

                // Décode la solution en vérifiant les préconditions et en appliquant les effets
                Plan plan = decodeSolution(solver.model(), problem);
                this.getStatistics().setTimeToSearch(solver.getTimeout());
                return plan;
            } else {
                LOGGER.info("* SAT search failed\n");
                return null;
            }
        } catch (ContradictionException e) {
            LOGGER.error("SAT problem has a contradiction!", e);
            return null;
        } catch (OutOfMemoryError e) {
            LOGGER.error("Problème trop grand pour la mémoire actuelle.");
            System.err.println("Erreur de mémoire.");
            return null;
        } catch (TimeoutException e) {
            LOGGER.error("SAT solver timeout exceeded!", e);
            return null;
        }
    }



        private void encodeInitialState(Problem problem, ISolver solver) throws ContradictionException {
            BitVector initialState = problem.getInitialState().getPositiveFluents();
            for (int i = 0; i < initialState.size(); i++) {
                if (initialState.get(i)) { 
                    int var = fluentToVar(i, 0,problem); 
                    solver.addClause(new VecInt(new int[] { var }));
                }
            }
        }

        private void encodeActions(Problem problem, ISolver solver) throws ContradictionException {
            for (Action action : problem.getActions()) {
                int actionId = getActionId(action);

                if (action.getPrecondition() != null) {
                    BitVector preconditions = action.getPrecondition().getPositiveFluents();
                    for (int i = 0; i < preconditions.size(); i++) {
                        if (preconditions.get(i)) {
                            int var = fluentToVar(i, actionId, problem); 
                            LOGGER.info("Action: " + action.getName() + " Precondition: " + problem.getFluents().get(i) + " Var: " + var + "\n");
                            solver.addClause(new VecInt(new int[] { -actionId, var })); 
                        }
                    }
                }

                for (ConditionalEffect condEffect : action.getConditionalEffects()) {
                    Effect effect = condEffect.getEffect();
                    BitVector positiveEffects = effect.getPositiveFluents();
                    for (int i = 0; i < positiveEffects.size(); i++) {
                        if (positiveEffects.get(i)) {
                            if (problem.getGoal().getPositiveFluents().get(i)) {
                                int var = fluentToVar(i, actionId + 1, problem);
                                solver.addClause(new VecInt(new int[] { -actionId, var })); 
                            }
                        }
                    }
                }
            }
        }

        private void encodeGoalState(Problem problem, ISolver solver) throws ContradictionException {
            BitVector goalState = problem.getGoal().getPositiveFluents();
            for (int i = 0; i < goalState.size(); i++) {
                if (goalState.get(i)) {
                    int var = fluentToVar(i, Integer.MAX_VALUE,problem);
                    solver.addClause(new VecInt(new int[] { var }));
                }
            }
        }

        private Plan decodeSolution(int[] model, Problem problem) {
            Plan plan = new SequentialPlan();
            BitVector currentState = problem.getInitialState().getPositiveFluents();  // L'état initial
        
            for (int var : model) {
                if (var > 0) { 
                    // On récupère l'action associée à la variable
                    Action action = getActionByVar(var);
        
                    if (action != null) {
                        // Vérifier si les préconditions de l'action sont satisfaites dans l'état courant
                        if (checkPreconditions(action, currentState, problem)) {
                            // Si les préconditions sont satisfaites, ajouter l'action au plan
                            plan.add(0, action);
        
                            // Appliquer les effets positifs et négatifs de l'action
                            applyEffects(action, currentState, problem);
                        } else {
                            // Si les préconditions ne sont pas satisfaites, ignorer cette solution
                            LOGGER.warn("Action {} ne respecte pas les préconditions", action.getName());
                        }
                    }
                }
            }
            return plan;
        }

        private boolean checkPreconditions(Action action, BitVector currentState, Problem problem) {
            if (action.getPrecondition() != null) {
                BitVector preconditions = action.getPrecondition().getPositiveFluents();
                for (int i = 0; i < preconditions.size(); i++) {
                    if (preconditions.get(i) && !currentState.get(i)) {
                        // Si une précondition est positive et non satisfaite, l'action ne peut pas être exécutée
                        return false;
                    }
                }
            }
            return true;
        }

        private void applyEffects(Action action, BitVector currentState, Problem problem) {
            // Appliquer les effets classiques (non conditionnels)
            for (ConditionalEffect effect : action.getConditionalEffects()) {
                BitVector positiveEffects = effect.getEffect().getPositiveFluents();
                for (int i = 0; i < positiveEffects.size(); i++) {
                    if (positiveEffects.get(i)) {
                        currentState.set(i);  // Marquer le fluent comme vrai
                    }
                }
        
                BitVector negativeEffects = effect.getEffect().getNegativeFluents();
                for (int i = 0; i < negativeEffects.size(); i++) {
                    if (negativeEffects.get(i)) {
                        currentState.clear(i);  // Marquer le fluent comme faux
                    }
                }
            }
        
            // Appliquer les effets conditionnels
            for (ConditionalEffect conditionalEffect : action.getConditionalEffects()) {
                // Condition de l'effet conditionnel
                BitVector condition = conditionalEffect.getCondition().getPositiveFluents();
                boolean conditionMet = true;
        
                // Vérifier si la condition est satisfaite
                for (int i = 0; i < condition.size(); i++) {
                    if (condition.get(i) && !currentState.get(i)) {
                        conditionMet = false;
                        break;
                    }
                }
        
                if (conditionMet) {
                    // Si la condition est satisfaite, appliquer les effets de l'effet conditionnel
                    Effect effect = conditionalEffect.getEffect();
                    BitVector positiveEffects = effect.getPositiveFluents();
                    for (int i = 0; i < positiveEffects.size(); i++) {
                        if (positiveEffects.get(i)) {
                            currentState.set(i);  // Marquer le fluent comme vrai
                        }
                    }
        
                    BitVector negativeEffects = effect.getNegativeFluents();
                    for (int i = 0; i < negativeEffects.size(); i++) {
                        if (negativeEffects.get(i)) {
                            currentState.clear(i);  // Marquer le fluent comme faux
                        }
                    }
                }
            }
        }
        
        
        
    

    private Action getActionByVar(int var) {
        for (Map.Entry<Action, Integer> entry : actionIds.entrySet()) {
            if (entry.getValue().equals(var)) {
                return entry.getKey();
            }
        }
        return null;
    }

    private int fluentToVar(int fluentId, int timeStep, Problem problem) {
        if (fluentId < 0 || timeStep < 0) {
            throw new IllegalArgumentException("Fluent ID must be positive");
        }
        return 1 + (timeStep * 1500) + fluentId; 
    }

    /**
     * Returns if a specified problem is supported by the planner. Just ADL problem
     * can be solved by this planner.
     *
     * @param problem the problem to test.
     * @return <code>true</code> if the problem is supported <code>false</code>
     *         otherwise.
     */
    @Override
    public boolean isSupported(Problem problem) {
        return !problem.getRequirements().contains(RequireKey.ACTION_COSTS)
                && !problem.getRequirements().contains(RequireKey.CONSTRAINTS)
                && !problem.getRequirements().contains(RequireKey.CONTINOUS_EFFECTS)
                && !problem.getRequirements().contains(RequireKey.DERIVED_PREDICATES)
                && !problem.getRequirements().contains(RequireKey.DURATIVE_ACTIONS)
                && !problem.getRequirements().contains(RequireKey.DURATION_INEQUALITIES)
                && !problem.getRequirements().contains(RequireKey.FLUENTS)
                && !problem.getRequirements().contains(RequireKey.GOAL_UTILITIES)
                && !problem.getRequirements().contains(RequireKey.METHOD_CONSTRAINTS)
                && !problem.getRequirements().contains(RequireKey.NUMERIC_FLUENTS)
                && !problem.getRequirements().contains(RequireKey.OBJECT_FLUENTS)
                && !problem.getRequirements().contains(RequireKey.PREFERENCES)
                && !problem.getRequirements().contains(RequireKey.TIMED_INITIAL_LITERALS)
                && !problem.getRequirements().contains(RequireKey.HIERARCHY);
    }

    /**
     * The main method of the <code>ASP</code> planner.
     *
     * @param args the arguments of the command line.
     */
    public static void main(String[] args) {
        try {
            final SAT planner = new SAT();
            CommandLine cmd = new CommandLine(planner);
            cmd.execute(args);
        } catch (IllegalArgumentException e) {
            LOGGER.fatal(e.getMessage());
        }
    }

    /**
     * Returns the name of the heuristic used by the planner to solve a planning
     * problem.
     *
     * @return the name of the heuristic used by the planner to solve a planning
     *         problem.
     */
    public final StateHeuristic.Name getHeuristic() {
        return this.heuristic;
    }

    /**
     * Returns the weight of the heuristic.
     *
     * @return the weight of the heuristic.
     */
    public final double getHeuristicWeight() {
        return this.heuristicWeight;
    }

    /**
     * Sets the weight of the heuristic.
     *
     * @param weight the weight of the heuristic. The weight must be greater than 0.
     * @throws IllegalArgumentException if the weight is strictly less than 0.
     */
    @CommandLine.Option(names = { "-w",
            "--weight" }, defaultValue = "1.0", paramLabel = "<weight>", description = "Set the weight of the heuristic (preset 1.0).")
    public void setHeuristicWeight(final double weight) {
        if (weight <= 0) {
            throw new IllegalArgumentException("Weight <= 0");
        }
        this.heuristicWeight = weight;
    }

    /**
     * Set the name of heuristic used by the planner to the solve a planning
     * problem.
     *
     * @param heuristic the name of the heuristic.
     */
    @CommandLine.Option(names = { "-e",
            "--heuristic" }, defaultValue = "FAST_FORWARD", description = "Set the heuristic : AJUSTED_SUM, AJUSTED_SUM2, AJUSTED_SUM2M, COMBO, "
                    + "MAX, FAST_FORWARD SET_LEVEL, SUM, SUM_MUTEX (preset: FAST_FORWARD)")
    public void setHeuristic(StateHeuristic.Name heuristic) {
        this.heuristic = heuristic;
    }
}
