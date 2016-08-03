/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package de.matul.lightup.demo;

import java.awt.Component;
import java.awt.Point;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;

import javax.swing.Timer;

public class MouseHover extends MouseAdapter implements ActionListener {

    private Timer timer;
    private boolean active;
    private boolean entered;
    private Point curPoint;
    private Component component;

    public MouseHover(Component component, int delay) {
        this.component = component;
        this.timer = new Timer(delay, this);
    }

    @Override
    public void mouseMoved(MouseEvent e) {
        if(entered && dist2(e.getPoint(), curPoint) > 25) {
            timer.restart();
            curPoint = e.getPoint();
        }
    }

    private int dist2(Point p1, Point p2) {
        int dx = p1.x-p2.x;
        int dy = p1.y-p2.y;
        return dx*dx + dy*dy;
    }

    @Override
    public void mouseEntered(MouseEvent e) {
        if(active) {
            entered = true;
            curPoint = e.getPoint();
            timer.restart();
        }
    }

    @Override
    public void mouseExited(MouseEvent e) {
        entered = false;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        if(active) {
            MouseEvent mouseEvent = new MouseEvent(component, 1000, System.currentTimeMillis(), 0,
                    curPoint.x, curPoint.y, 0, 0, 1, false, 0);
            for (MouseListener listener : component.getMouseListeners()) {
                listener.mouseClicked(mouseEvent);
            }
        }
        timer.stop();
    }

    public void start() {
        component.addMouseListener(this);
        component.addMouseMotionListener(this);
        active = true;
    }

}
