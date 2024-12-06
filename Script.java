import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.InputStreamReader;
import java.util.logging.Logger;
import java.io.IOException;
import java.io.File;

public class Script {

    public static void main(String[] args) {
        // Définition des variables pour la commande
        String domain = "domain.pddl";
        String lien = ".\\src\\test\\resources\\benchmarks\\pddl\\";
        String lien2 = "ipc1998\\gripper\\adl\\";
        boolean mctsOuAsp = true;
        String SATsolver = "fr.uga.pddl4j.examples.asp.SATsolver";
        String aStar = "fr.uga.pddl4j.examples.asp.HSP";

        for (int domainIndex = 1; domainIndex <=5; domainIndex++) {
            for(int j=0; j<2; j++){
            String problem = domainIndex+".pddl";
        
            
        String className = mctsOuAsp ? SATsolver : aStar;
        String[] command = {
            "java",
            "-cp",
            "classes;lib/pddl4j-4.0.0.jar;lib/org.sat4j.core.jar",
            className,
            lien + lien2 + domain,
            lien + lien2 + "p0" + problem
        };
        try {
            // Utilisation de ProcessBuilder pour exécuter la commande dans PowerShell
            ProcessBuilder processBuilder = new ProcessBuilder(command);
            processBuilder.directory(new File("C:\\Users\\Chrom\\Documents\\M2_IC\\PlaniAuto\\TP3\\PlaniTP3"));

            // Lancement de la commande
            Process process = processBuilder.start();
            System.out.println("Exécution de la commande: " + command);
            System.out.println("Sortie de la commande:\n");

            // Threads pour lire la sortie standard et le flux d'erreur en parallèle
            StringBuilder output = new StringBuilder();

            Thread outputThread = new Thread(() -> {
                try (BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()))) {
                    String line;
                    while ((line = reader.readLine()) != null) {
                        output.append(line).append("\n");
                        System.out.println("OUTPUT: " + line); // Affichage de la sortie standard en direct
                    }
                } catch (IOException e) {
                    e.printStackTrace();
                }
            });

            Thread errorThread = new Thread(() -> {
                try (BufferedReader reader = new BufferedReader(new InputStreamReader(process.getErrorStream()))) {
                    String line;
                    while ((line = reader.readLine()) != null) {
                        System.err.println("ERROR: " + line); // Affichage du flux d'erreur en direct
                    }
                } catch (IOException e) {
                    e.printStackTrace();
                }
            });

            // Lancer les threads pour lire les sorties
            outputThread.start();
            errorThread.start();

            // Attendre la fin du processus et des threads de sortie
            int exitCode = process.waitFor();
            outputThread.join();
            errorThread.join();

            if (exitCode == 0) {
                System.out.println("La commande a été exécutée avec succès!");

                // Analyse de la sortie pour trouver "Total time" et la ligne précédant "Time spent"
                String[] lines = output.toString().split("\n");
                String totalTimeLine = null;
                String lineBeforeTimeSpent = null;

                for (int i = 0; i < lines.length; i++) {
                    if (lines[i].contains("total time")) {
                        totalTimeLine = lines[i];
                    }
                    if (i > 0 && lines[i].contains("time spent:")) {
                        String line = lines[i-2];
                        int index = line.indexOf(":");
                        lineBeforeTimeSpent = line.substring(0, index);
                        
                        int lineBeforeTimeSpentInt = Integer.parseInt(lineBeforeTimeSpent) + 1;
                        System.out.println("Nombre d'actions: " + lineBeforeTimeSpentInt);
                        lineBeforeTimeSpent = Integer.toString(lineBeforeTimeSpentInt);
                    }
                }

                // Écriture dans le fichier stat.txt
                try (BufferedWriter writer = new BufferedWriter(new FileWriter("stat.txt",true))) {

                    writer.write(mctsOuAsp ? "SAT\n" : "HSP\n");
                    writer.write("Domaine: " + domain + ", Problème: " + problem + "\n");
                    writer.write("Total time: " + (totalTimeLine != null ? totalTimeLine : "Non trouvé") + "\n");
                    writer.write("Nombre d'actions: " + (lineBeforeTimeSpent != null ? lineBeforeTimeSpent : "Non trouvé") + "\n");
                    System.out.println("Les statistiques ont été écrites dans stat.txt.");
                } catch (IOException e) {
                    System.err.println("Erreur lors de l'écriture dans le fichier : " + e.getMessage());
                }

            } else {
                System.out.println("Erreur lors de l'exécution de la commande, code de sortie : " + exitCode);
            }
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
        }
        mctsOuAsp = !mctsOuAsp;
    }
        
    }
}
}
