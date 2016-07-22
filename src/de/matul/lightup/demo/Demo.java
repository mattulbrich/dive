/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package de.matul.lightup.demo;

import java.awt.Color;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.Random;

import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTextArea;
import javax.swing.ListSelectionModel;
import javax.swing.SwingUtilities;
import javax.swing.WindowConstants;

import de.matul.lightup.LightupConnection;
import de.matul.lightup.LightupElement;
import de.matul.lightup.LightupManager;

public class Demo extends JFrame {

    public static void main(String[] args) {
        Demo d = new Demo();
        d.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);
        d.setVisible(true);
    }


    private JList<WordLightupElement> list;
    private JTextArea text;
    private LightupManager lightupManager = new LightupManager();

    private LightupConnection[] connectionsPerWord;

    private MouseListener mouseInList = new MouseAdapter() {

        public void mouseClicked(MouseEvent e) {
            if(e.getClickCount() >= 2) {
                WordLightupElement val = list.getSelectedValue();
                if(val == null) {
                    return;
                }

                LightupConnection conn = connectionsPerWord[val.getNumber()];
                if(conn != null) {
                    lightupManager.hideConnection(conn);
                    connectionsPerWord[val.getNumber()] = null;
                } else {
                    conn = new LightupConnection(val, val);
                    conn.setColor(Color.red);
                    conn.setProperty(LightupConnection.BG_COLOR_PROPERTY, new Color(255,200,200));
                    lightupManager.showConnection(conn);
                    connectionsPerWord[val.getNumber()] = conn;
                }

                list.repaint();
            }
        };
    };

    private MouseListener mouseOverText = new MouseAdapter() {
        private LightupConnection connection;

        @Override
        public void mouseClicked(MouseEvent e) {
            if(e.getID() != 1000) {
                return;
            }

            if(connection != null) {
                lightupManager.hideConnection(connection);
            }

            int mousePos = text.viewToModel(e.getPoint());
            int pos = 0;
            int beg = pos;
            int count = -1;
            String s = text.getText();
            while(pos < mousePos) {
                beg = pos;
                pos = s.indexOf(' ', pos + 1);
                count++;
            }

            LightupElement elem = new WordLightupElement(s.substring(beg+1, pos), count);
            connection = new LightupConnection(elem, elem);
            connection.setColor(Color.green);
            connection.setProperty(LightupConnection.BG_COLOR_PROPERTY, new Color(200, 255, 200));
            lightupManager.showConnection(connection);

            System.err.println(connection);
        };

        @Override
        public void mouseExited(MouseEvent e) {
            if(connection != null) {
                lightupManager.hideConnection(connection);
                connection = null;
            }
        }
    };

    public Demo() {
        super("Demo - Lightup");

        String bogusText = bogus(500);
        WordLightupElement[] elements = makeElements(bogusText.split(" "));
        connectionsPerWord = new LightupConnection[elements.length];

        JSplitPane split = new JSplitPane();
        list = new JList<>(elements);
        list.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        ListLightupListener listener = new ListLightupListener(list, connectionsPerWord);
        lightupManager.addLightupListener(listener);
        list.setCellRenderer(new WordCellRenderer(lightupManager, connectionsPerWord));
        split.setLeftComponent(new JScrollPane(list));

        list.addMouseListener(mouseInList);

        text = new JTextArea(bogusText);
        text.setLineWrap(true);
        text.setEditable(false);
        text.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 14));
        lightupManager.addLightupListener(new TextAreaLightupListener(text));
        split.setRightComponent(new JScrollPane(text));

        new MouseHover(text, 400).start();

        text.addMouseListener(mouseOverText );

        getContentPane().add(split);
        setSize(800, 600);
        split.setDividerLocation(200);

        setGlassPane(new JComponent() {

            @Override
            protected void paintComponent(Graphics g) {
                g.drawLine(100,100, 300, 300);
            }

        });

        getGlassPane().setVisible(true);
    }

    private WordLightupElement[] makeElements(String[] words) {
        WordLightupElement[] result = new WordLightupElement[words.length];
        for (int i = 0; i < result.length; i++) {
            result[i] = new WordLightupElement(words[i], i);
        }
        return result;
    }


    public static String bogus(int words) {
        StringBuilder sb = new StringBuilder();
        Random r = new Random();

        for (int i = 0; i < words; i++) {
            int l = r.nextInt(10) + 1;
            for (int j = 0; j < l; j++) {
                char c = (char) ('a' + r.nextInt(26));
                sb.append(c);
            }
            sb.append(" ");
        }
        return sb.toString();
    }

}
