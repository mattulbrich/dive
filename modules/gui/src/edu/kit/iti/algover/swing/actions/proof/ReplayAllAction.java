/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.actions.proof;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.swing.actions.BarAction;
import edu.kit.iti.algover.swing.actions.BarManager.Initialisable;
import edu.kit.iti.algover.swing.util.ConcurrentCounter;
import edu.kit.iti.algover.swing.util.Log;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.stream.Collectors;

public class ReplayAllAction extends BarAction implements Initialisable {

    @Override
    public void actionPerformed(ActionEvent e) {
        List<Proof> proofs = computeProofs();
        ProgressMonitor pm = new ProgressMonitor(getParentFrame(), "Replaying proofs", "Note", 0, proofs.size());
        ConcurrentCounter counter = new ConcurrentCounter();
        counter.addListener(c -> counterAction(c, pm));
        ExecutorService executor = getDiveCenter().getExecutor();

        getDiveCenter().properties().onGoingProof.setValue(true);
        for (Proof proof : proofs) {
            executor.submit(() -> replay(pm, proof, counter));
        }
    }

    private void counterAction(int count, ProgressMonitor pm) {
        pm.setProgress(count);
        if (pm.getMaximum() == count) {
            pm.close();
            getDiveCenter().properties().onGoingProof.setValue(false);
        } else {
            getDiveCenter().properties().onGoingProof.fire(true);
        }
    }


    private List<Proof> computeProofs() {
        Collection<Proof> allProofs = getDiveCenter().getProjectManager().getAllProofs().values();
        return allProofs.stream().filter(ReplayAllAction::isDirty).collect(Collectors.toList());
    }

    private static boolean isDirty(Proof proof) {
        ProofStatus state = proof.getProofStatus();
        return  state == ProofStatus.DIRTY ||
                state == ProofStatus.CHANGED_SCRIPT ||
                state == ProofStatus.NON_EXISTING;
    }

    @Override
    public void initialised() {
        getDiveCenter().properties().noProjectMode.addObserver(noProj -> setEnabled(!noProj));
    }

    private void replay(ProgressMonitor pm, Proof proof, ConcurrentCounter counter) {
        try {
            Log.enter(proof, counter);
            if(!pm.isCanceled()) {
                String script = proof.getScript();
                if (script == null || script.trim().isEmpty()) {
                    script = getDiveCenter().properties().project.getValue().
                            getSettings().getString(ProjectSettings.DEFAULT_SCRIPT);
                    proof.setScriptText(script);
                }

                proof.interpretScript();
                System.err.println(proof.getFailException());
            }
            // TODO remove default script if it does not work?
        } catch(Exception ex) {
            Log.stacktrace(Log.TRACE, ex);
        } finally {
            counter.increment();
            Log.leave();
        }
    }
}
