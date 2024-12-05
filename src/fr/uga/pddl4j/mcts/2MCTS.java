package fr.uga.pddl4j.mcts;

import fr.uga.pddl4j.heuristics.state.StateHeuristic;
import fr.uga.pddl4j.parser.DefaultParsedProblem;
import fr.uga.pddl4j.parser.RequireKey;
import fr.uga.pddl4j.plan.Plan;
import fr.uga.pddl4j.plan.SequentialPlan;
import fr.uga.pddl4j.planners.AbstractPlanner;
import fr.uga.pddl4j.planners.Planner;
import fr.uga.pddl4j.planners.PlannerConfiguration;
import fr.uga.pddl4j.planners.ProblemNotSupportedException;
import fr.uga.pddl4j.planners.SearchStrategy;
import fr.uga.pddl4j.planners.statespace.search.StateSpaceSearch;
import fr.uga.pddl4j.planners.Statistics;
import fr.uga.pddl4j.planners.statespace.HSP;
import fr.uga.pddl4j.problem.*;
import fr.uga.pddl4j.planners.InvalidConfigurationException;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.ConditionalEffect;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import picocli.CommandLine;

import java.io.*;
import java.util.*;


/**
 * This class is a model of the Monte-Carlo search planner.
 *
 * @author 
 */
@CommandLine.Command(name = "MCTS",
version = "MCTS 1.0",
description = "Solves a specified planning problem using Monte Carlo Tree Search.",
sortOptions = false,
mixinStandardHelpOptions = true,
headerHeading = "Usage:%n",
synopsisHeading = "%n",
descriptionHeading = "%nDescription:%n%n",
parameterListHeading = "%nParameters:%n",
optionListHeading = "%nOptions:%n")
public class MCTS extends AbstractPlanner {
	/**
	 * The class logger.
	 */
	private static final Logger LOGGER = LogManager.getLogger(MCTS.class.getName());

    /**
     * The HEURISTIC property used for planner configuration.
     */
    public static final String HEURISTIC_SETTING = "HEURISTIC";

    /**
     * The default value of the HEURISTIC property used for planner configuration.
     */
    public static final StateHeuristic.Name DEFAULT_HEURISTIC = StateHeuristic.Name.FAST_FORWARD;

    /**
     * The WEIGHT_HEURISTIC property used for planner configuration.
     */
    public static final String WEIGHT_HEURISTIC_SETTING = "WEIGHT_HEURISTIC";

    /**
     * The default value of the WEIGHT_HEURISTIC property used for planner configuration.
     */
    public static final double DEFAULT_WEIGHT_HEURISTIC = 1.0;
	/**
	 * The weight of the heuristic.
	 */
	private double heuristicWeight = 1;

	/**
	 * The name of the heuristic used by the planner.
	 */
	private StateHeuristic.Name heuristic;

	/**
	 * The number of random walks.
	 */
	public static int NUM_WALK = 1000;

	/**
	 * The length of a random walk.
	 */
	public static int LENGTH_WALK = 8;

	/**
	 * The number of steps before restarting the search.
	 */
	public static long MAX_STEPS = 5;

    /**
     * Creates a new Monte-Carlo search planner with the default configuration.
     */
    public MCTS() {
        this(MCTS.getDefaultConfiguration());
    }

    /**
     * Creates a new Monte-Carlo search planner with a specified configuration.
     *
     * @param configuration the configuration of the planner.
     */
    public MCTS(final PlannerConfiguration configuration) {
        super();
        this.setConfiguration(configuration);
    }

    /**
     * Sets the weight of the heuristic.
     *
     * @param weight the weight of the heuristic. The weight must be greater than 0.
     * @throws IllegalArgumentException if the weight is strictly less than 0.
     */
    @CommandLine.Option(names = {"-w", "--weight"}, defaultValue = "1.0",
        paramLabel = "<weight>", description = "Set the weight of the heuristic (preset 1.0).")
    public void setHeuristicWeight(final double weight) {
        if (weight <= 0) {
            throw new IllegalArgumentException("Weight <= 0");
        }
        this.heuristicWeight = weight;
    }

    /**
     * Set the name of heuristic used by the planner to the solve a planning problem.
     *
     * @param heuristic the name of the heuristic.
     */
    @CommandLine.Option(names = {"-e", "--heuristic"}, defaultValue = "FAST_FORWARD",
        description = "Set the heuristic : AJUSTED_SUM, AJUSTED_SUM2, AJUSTED_SUM2M, COMBO, "
            + "MAX, FAST_FORWARD SET_LEVEL, SUM, SUM_MUTEX (preset: FAST_FORWARD)")
    public void setHeuristic(StateHeuristic.Name heuristic) {
        this.heuristic = heuristic;
    }

	/**
	 * Returns the name of the heuristic used by the planner to solve a planning problem.
	 *
	 * @return the name of the heuristic used by the planner to solve a planning problem.
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
	 * Instantiates the planning problem from a parsed problem.
	 *
	 * @param problem the problem to instantiate.
	 * @return the instantiated planning problem or null if the problem cannot be instantiated.
	 */
	@Override
	public Problem instantiate(DefaultParsedProblem problem) {
		final Problem pb = new DefaultProblem(problem);
		pb.instantiate();
		return pb;
	}

	/**
	 * Search a solution plan to a specified domain and problem using MCTS.
	 *
	 * @param problem the problem to solve.
	 * @return the plan found or null if no plan was found.
	 */
	@Override
    public Plan solve(final Problem problem) {
        // Creates the A* search strategy
        StateSpaceSearch search = StateSpaceSearch.getInstance(SearchStrategy.Name.MCTS,
            this.getHeuristic(), this.getHeuristicWeight(), this.getTimeout());
        LOGGER.info("* Starting MCTS search \n");
        // Search a solution
        Plan plan = search.searchPlan(problem);
        // If a plan is found update the statistics of the planner and log search information
        if (plan != null) {
            LOGGER.info("* MCTS search succeeded\n");
            this.getStatistics().setTimeToSearch(search.getSearchingTime());
            this.getStatistics().setMemoryUsedToSearch(search.getMemoryUsed());
        } else {
            LOGGER.info("* MCTS search failed\n");
        }
        // Return the plan found or null if the search fails.
        return plan;
    }
	
 /**
     * Checks the planner configuration and returns if the configuration is valid.
     * A configuration is valid if (1) the domain and the problem files exist and
     * can be read, (2) the timeout is greater than 0, (3) the weight of the
     * heuristic is greater than 0 and (4) the heuristic is a not null.
     *
     * @return <code>true</code> if the configuration is valid <code>false</code> otherwise.
     */
    public boolean hasValidConfiguration() {
        return super.hasValidConfiguration()
            && this.getHeuristicWeight() > 0.0
            && this.getHeuristic() != null;
    }
	
    /**
     * This method return the default arguments of the planner.
     *
     * @return the default arguments of the planner.
     * @see PlannerConfiguration
     */
    public static PlannerConfiguration getDefaultConfiguration() {
        PlannerConfiguration config = Planner.getDefaultConfiguration();
        config.setProperty(MCTS.HEURISTIC_SETTING, MCTS.DEFAULT_HEURISTIC.toString());
        config.setProperty(MCTS.WEIGHT_HEURISTIC_SETTING,
            Double.toString(MCTS.DEFAULT_WEIGHT_HEURISTIC));
        return config;
    }

    /**
     * Returns the configuration of the planner.
     *
     * @return the configuration of the planner.
     */
    @Override
    public PlannerConfiguration getConfiguration() {
        final PlannerConfiguration config = super.getConfiguration();
        config.setProperty(MCTS.HEURISTIC_SETTING, this.getHeuristic().toString());
        config.setProperty(MCTS.WEIGHT_HEURISTIC_SETTING, Double.toString(this.getHeuristicWeight()));
        return config;
    }

    /**
     * Sets the configuration of the planner. If a planner setting is not defined in
     * the specified configuration, the setting is initialized with its default value.
     *
     * @param configuration the configuration to set.
     */
    @Override
    public void setConfiguration(final PlannerConfiguration configuration) {
        super.setConfiguration(configuration);
        if (configuration.getProperty(MCTS.WEIGHT_HEURISTIC_SETTING) == null) {
            this.setHeuristicWeight(MCTS.DEFAULT_WEIGHT_HEURISTIC);
        } else {
            this.setHeuristicWeight(Double.parseDouble(configuration.getProperty(
                MCTS.WEIGHT_HEURISTIC_SETTING)));
        }
        if (configuration.getProperty(MCTS.HEURISTIC_SETTING) == null) {
            this.setHeuristic(MCTS.DEFAULT_HEURISTIC);
        } else {
            this.setHeuristic(StateHeuristic.Name.valueOf(configuration.getProperty(
                MCTS.HEURISTIC_SETTING)));
        }
    }

	/**
	 * The main method of the <code>MCTS</code> planner.
	 * Launch both MCTS and HSP on all the problems of the blocks, depot, gripper and logistics domains.
	 * Write the results in a csv file.
	 *
	 * @param args the arguments of the command line.
	 */
	public static void main(String[] args) {
        try {
            final MCTS planner = new MCTS();
            CommandLine cmd = new CommandLine(planner);
            cmd.execute(args);
        } catch (IllegalArgumentException e) {
            LOGGER.fatal(e.getMessage());
        }
    }

    public Plan mcts(Problem problem) throws ProblemNotSupportedException {
        // Check if the problem is supported by the planner
        if (!this.isSupported(problem)) {
            throw new ProblemNotSupportedException("Problem not supported");
        }

        // Initialize variables
        double hmin = Double.POSITIVE_INFINITY;
        State smin = null;

        // Get the initial state from the planning problem
        State init = new State(problem.getInitialState());

        // Start the MCTS search
        for (int i = 0; i < NUM_WALK; i++) {
            State s = init;
            for (int j = 0; j < LENGTH_WALK; j++) {
                List<Action> applicableActions = getApplicableActions(s, problem);
                if (applicableActions.isEmpty()) {
                    break;
                }
                Action a = uniformlyRandomSelectFrom(applicableActions);
                s = apply(s, a);
                if (s.satisfies(problem.getGoal())) {
                    return extractPlan(s, problem);
                }
            }
            double h = heuristic(s, problem.getGoal());
            if (h < hmin) {
                smin = s;
                hmin = h;
            }
        }

        if (smin == null) {
            return extractPlan(init, problem);
        } else {
            return extractPlan(smin, problem);
        }
    }

    private List<Action> getApplicableActions(State s, Problem problem) {
        List<Action> applicableActions = new ArrayList<>();
        for (Action a : problem.getActions()) {
            if (a.isApplicable(s)) {
                applicableActions.add(a);
            }
        }
        return applicableActions;
    }

    private Action uniformlyRandomSelectFrom(List<Action> actions) {
        Random random = new Random();
        return actions.get(random.nextInt(actions.size()));
    }

    private State apply(State s, Action a) {
        State newState = new State(s);
        for (ConditionalEffect ce : a.getConditionalEffects()) {
            if (s.satisfies(ce.getCondition())) {
                newState.apply(ce.getEffect());
            }
        }
        return newState;
    }

    private double heuristic(State s, Goal goal) {
        // Implement your heuristic function here
        return 0;
    }

    private Plan extractPlan(State s, Problem problem) {
        // Implement your plan extraction logic here
        return new Plan();
    }


	/**
	 * Returns if a specified problem is supported by the planner. Just ADL problem can be solved by this planner.
	 *
	 * @param problem the problem to test.
	 * @return <code>true</code> if the problem is supported <code>false</code> otherwise.
	 */
	@Override
	public boolean isSupported(Problem problem) {
		return (problem.getRequirements().contains(RequireKey.ACTION_COSTS)
				|| problem.getRequirements().contains(RequireKey.CONSTRAINTS)
				|| problem.getRequirements().contains(RequireKey.CONTINOUS_EFFECTS)
				|| problem.getRequirements().contains(RequireKey.DERIVED_PREDICATES)
				|| problem.getRequirements().contains(RequireKey.DURATIVE_ACTIONS)
				|| problem.getRequirements().contains(RequireKey.DURATION_INEQUALITIES)
				|| problem.getRequirements().contains(RequireKey.FLUENTS)
				|| problem.getRequirements().contains(RequireKey.GOAL_UTILITIES)
				|| problem.getRequirements().contains(RequireKey.METHOD_CONSTRAINTS)
				|| problem.getRequirements().contains(RequireKey.NUMERIC_FLUENTS)
				|| problem.getRequirements().contains(RequireKey.OBJECT_FLUENTS)
				|| problem.getRequirements().contains(RequireKey.PREFERENCES)
				|| problem.getRequirements().contains(RequireKey.TIMED_INITIAL_LITERALS)
				|| problem.getRequirements().contains(RequireKey.HIERARCHY))
				? false : true;
	}

}