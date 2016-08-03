package edu.kit.iti.algover.util;

public class Debug {


    public static CharSequence prettyPrint(CharSequence cs) {

        int len = cs.length();
        int level = 0;
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < len; i++) {

            char c = cs.charAt(i);
            switch(c) {
            case '(':
                level++;
                sb.append("\n").append(Util.duplicate(" ", level));
                break;
            case ')':
                level--;
                break;
            }
            sb.append(c);
        }

        return sb;

    }

}
