Le planner SAT se trouve dans le dossier PlaniTP3\src\fr\uga\pddl4j\examples\asp et se nomme SATsolver.java
Pour compiler le planner, se placer à la racine du projet et lancer la commande : 
    "javac -d classes -cp "lib/pddl4j-4.0.0.jar;lib/org.sat4j.core.jar" .\src\fr\uga\pddl4j\examples\asp\*.java .\src\fr\uga\pddl4j\examples\asp\Node.java"

Le planner SAT peut être lancé manuellement avec n'importe quel domaine et problème associé en executant la commande : 
    "java -cp "classes;lib/pddl4j-4.0.0.jar;lib/org.sat4j.core.jar" fr.uga.pddl4j.examples.asp.SAT <Domain.pddl> <Problem.pddl>" 
( un exemple de domaine et de problème étant ".\src\test\resources\adl\domain.pddl" pour le domaine et ".\src\test\resources\benchmarks\pddl\ipc1998\logistics\adl\p01.pddl" )

les types de problèmes sont disponibles dans le dossier src/test/

Le rapport sur les comparaisons et l'exercice 2 sont dans le fichier Rapport.ipynb ( ou Rapport.pdf s'il existe )