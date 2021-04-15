import java.io.BufferedReader;
import java.io.InputStreamReader;

public class Problem14 {
	static BufferedReader stdin = new BufferedReader(new InputStreamReader(System.in));

	private String[] inputs = {"K","L","C","F","J","I","A","G","O","H","B","D","E","N","M"};

	public String a648437939 = "g";
	public String a625366011 = "i";
	public int a948298434 = 7;
	public String a674877 = "f";
	public String a1245641101 = "e";
	public int a37252965 = 12;
	public String a1114110175 = "f";
	public String a274626616 = "f";
	public int a1729378197 = 5;
	public int a871304185 = 10;
	public int a1518235786 = 7;
	public int a1920565083 = 10;
	public int a1803458941 = 15;
	public int a541989745 = 7;
	public String a1570444282 = "i";
	public String a1583272058 = "h";
	public int a1892947393 = 11;
	public int a1091978491 = 15;
	public int a1668586383 = 9;
	public String a68550605 = "f";
	public int a312388145 = 7;
	public String a847841994 = "i";
	public String a520547452 = "e";
	public int a23351479 = 10;
	public int a1853964249 = 6;
	public String a750845785 = "f";
	public int a310220227 = 10;
	public int a198422080 = 6;
	public int a1716763601 = 7;
	public int a1075056448 = 9;
	public boolean cf = true;
	public String a583157892 = "i";
	public int a299375216 = 8;
	public String a911974320 = "e";
	public String a1039409491 = "e";
	public int a938681481 = 8;
	public String a839019366 = "e";
	public String a1937499914 = "i";
	public int a520438996 = 9;
	public String a1047798024 = "i";
	public String a1466114073 = "e";
	public String a1105727296 = "f";
	public String a1306585414 = "i";
	public String a853421711 = "h";
	public int a50296898 = 13;
	public String a1584317767 = "f";
	public int a1105418891 = 7;
	public String a1477849038 = "g";
	public String a650861711 = "i";
	public String a366362113 = "e";
	public String a24442901 = "h";
	public String a145848903 = "h";
	public String a1716858626 = "h";
	public String a123124249 = "f";

	private void errorCheck() {
	    if((((a312388145 == 6) && (a1920565083 == 11)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(0);
	    }
	    if((((a1518235786 == 8) && (a1920565083 == 13)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(1);
	    }
	    if((((a1853964249 == 8) && (a938681481 == 8)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(2);
	    }
	    if((((a145848903.equals("i")) && (a123124249.equals("e"))) && (a1729378197 == 3))){
	    	cf = false;
	    	Errors.__VERIFIER_error(3);
	    }
	    if((((a1892947393 == 12) && (a938681481 == 11)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(4);
	    }
	    if((((a911974320.equals("e")) && (a938681481 == 9)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(5);
	    }
	    if((((a50296898 == 8) && (a1477849038.equals("i"))) && (a1729378197 == 4))){
	    	cf = false;
	    	Errors.__VERIFIER_error(6);
	    }
	    if((((a1466114073.equals("i")) && (a938681481 == 6)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(7);
	    }
	    if((((a1105727296.equals("i")) && (a299375216 == 5)) && (a1729378197 == 8))){
	    	cf = false;
	    	Errors.__VERIFIER_error(8);
	    }
	    if((((a198422080 == 9) && (a123124249.equals("h"))) && (a1729378197 == 3))){
	    	cf = false;
	    	Errors.__VERIFIER_error(9);
	    }
	    if((((a1583272058.equals("i")) && (a1047798024.equals("e"))) && (a1729378197 == 6))){
	    	cf = false;
	    	Errors.__VERIFIER_error(10);
	    }
	    if((((a1584317767.equals("g")) && (a123124249.equals("f"))) && (a1729378197 == 3))){
	    	cf = false;
	    	Errors.__VERIFIER_error(11);
	    }
	    if((((a839019366.equals("e")) && (a23351479 == 13)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(12);
	    }
	    if((((a853421711.equals("e")) && (a299375216 == 8)) && (a1729378197 == 8))){
	    	cf = false;
	    	Errors.__VERIFIER_error(13);
	    }
	    if((((a1091978491 == 10) && (a123124249.equals("g"))) && (a1729378197 == 3))){
	    	cf = false;
	    	Errors.__VERIFIER_error(14);
	    }
	    if((((a1075056448 == 9) && (a938681481 == 12)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(15);
	    }
	    if((((a1091978491 == 13) && (a123124249.equals("g"))) && (a1729378197 == 3))){
	    	cf = false;
	    	Errors.__VERIFIER_error(16);
	    }
	    if((((a1668586383 == 5) && (a1920565083 == 8)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(17);
	    }
	    if((((a1091978491 == 12) && (a123124249.equals("g"))) && (a1729378197 == 3))){
	    	cf = false;
	    	Errors.__VERIFIER_error(18);
	    }
	    if((((a1668586383 == 4) && (a1920565083 == 8)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(19);
	    }
	    if((((a145848903.equals("g")) && (a123124249.equals("e"))) && (a1729378197 == 3))){
	    	cf = false;
	    	Errors.__VERIFIER_error(20);
	    }
	    if((((a520438996 == 9) && (a23351479 == 11)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(21);
	    }
	    if((((a541989745 == 9) && (a1477849038.equals("g"))) && (a1729378197 == 2))){
	    	cf = false;
	    	Errors.__VERIFIER_error(22);
	    }
	    if((((a847841994.equals("e")) && (a299375216 == 1)) && (a1729378197 == 8))){
	    	cf = false;
	    	Errors.__VERIFIER_error(23);
	    }
	    if((((a1803458941 == 14) && (a23351479 == 12)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(24);
	    }
	    if((((a24442901.equals("g")) && (a1047798024.equals("f"))) && (a1729378197 == 6))){
	    	cf = false;
	    	Errors.__VERIFIER_error(25);
	    }
	    if((((a839019366.equals("g")) && (a23351479 == 13)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(26);
	    }
	    if((((a541989745 == 6) && (a1477849038.equals("g"))) && (a1729378197 == 2))){
	    	cf = false;
	    	Errors.__VERIFIER_error(27);
	    }
	    if((((a674877.equals("g")) && (a1477849038.equals("e"))) && (a1729378197 == 2))){
	    	cf = false;
	    	Errors.__VERIFIER_error(28);
	    }
	    if((((a1047798024.equals("i")) && (a299375216 == 2)) && (a1729378197 == 8))){
	    	cf = false;
	    	Errors.__VERIFIER_error(29);
	    }
	    if((((a145848903.equals("e")) && (a123124249.equals("e"))) && (a1729378197 == 3))){
	    	cf = false;
	    	Errors.__VERIFIER_error(30);
	    }
	    if((((a1584317767.equals("e")) && (a1477849038.equals("g"))) && (a1729378197 == 4))){
	    	cf = false;
	    	Errors.__VERIFIER_error(31);
	    }
	    if((((a1584317767.equals("f")) && (a123124249.equals("f"))) && (a1729378197 == 3))){
	    	cf = false;
	    	Errors.__VERIFIER_error(32);
	    }
	    if((((a1584317767.equals("h")) && (a1477849038.equals("g"))) && (a1729378197 == 4))){
	    	cf = false;
	    	Errors.__VERIFIER_error(33);
	    }
	    if((((a1716763601 == 7) && (a938681481 == 7)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(34);
	    }
	    if((((a198422080 == 9) && (a938681481 == 10)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(35);
	    }
	    if((((a520547452.equals("e")) && (a1477849038.equals("i"))) && (a1729378197 == 2))){
	    	cf = false;
	    	Errors.__VERIFIER_error(36);
	    }
	    if((((a911974320.equals("i")) && (a938681481 == 9)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(37);
	    }
	    if((((a1584317767.equals("e")) && (a123124249.equals("f"))) && (a1729378197 == 3))){
	    	cf = false;
	    	Errors.__VERIFIER_error(38);
	    }
	    if((((a50296898 == 13) && (a1477849038.equals("i"))) && (a1729378197 == 4))){
	    	cf = false;
	    	Errors.__VERIFIER_error(39);
	    }
	    if((((a520438996 == 4) && (a23351479 == 11)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(40);
	    }
	    if((((a583157892.equals("i")) && (a23351479 == 16)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(41);
	    }
	    if((((a583157892.equals("h")) && (a23351479 == 16)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(42);
	    }
	    if((((a1570444282.equals("h")) && (a1477849038.equals("f"))) && (a1729378197 == 4))){
	    	cf = false;
	    	Errors.__VERIFIER_error(43);
	    }
	    if((((a50296898 == 14) && (a1477849038.equals("i"))) && (a1729378197 == 4))){
	    	cf = false;
	    	Errors.__VERIFIER_error(44);
	    }
	    if((((a1716763601 == 3) && (a938681481 == 7)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(45);
	    }
	    if((((a1668586383 == 6) && (a1920565083 == 8)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(46);
	    }
	    if((((a198422080 == 7) && (a938681481 == 10)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(47);
	    }
	    if((((a1306585414.equals("f")) && (a299375216 == 7)) && (a1729378197 == 8))){
	    	cf = false;
	    	Errors.__VERIFIER_error(48);
	    }
	    if((((a948298434 == 14) && (a23351479 == 15)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(49);
	    }
	    if((((a1105418891 == 8) && (a1920565083 == 15)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(50);
	    }
	    if((((a948298434 == 10) && (a23351479 == 15)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(51);
	    }
	    if((((a648437939.equals("e")) && (a1477849038.equals("h"))) && (a1729378197 == 2))){
	    	cf = false;
	    	Errors.__VERIFIER_error(52);
	    }
	    if((((a68550605.equals("e")) && (a1920565083 == 14)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(53);
	    }
	    if((((a520438996 == 7) && (a23351479 == 11)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(54);
	    }
	    if((((a1105418891 == 11) && (a1920565083 == 15)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(55);
	    }
	    if((((a1570444282.equals("i")) && (a1477849038.equals("f"))) && (a1729378197 == 4))){
	    	cf = false;
	    	Errors.__VERIFIER_error(56);
	    }
	    if((((a23351479 == 16) && (a1047798024.equals("g"))) && (a1729378197 == 6))){
	    	cf = false;
	    	Errors.__VERIFIER_error(57);
	    }
	    if((((a198422080 == 10) && (a123124249.equals("h"))) && (a1729378197 == 3))){
	    	cf = false;
	    	Errors.__VERIFIER_error(58);
	    }
	    if((((a911974320.equals("f")) && (a938681481 == 9)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(59);
	    }
	    if((((a145848903.equals("f")) && (a123124249.equals("e"))) && (a1729378197 == 3))){
	    	cf = false;
	    	Errors.__VERIFIER_error(60);
	    }
	    if((((a911974320.equals("h")) && (a1047798024.equals("i"))) && (a1729378197 == 6))){
	    	cf = false;
	    	Errors.__VERIFIER_error(61);
	    }
	    if((((a1803458941 == 16) && (a23351479 == 12)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(62);
	    }
	    if((((a1892947393 == 11) && (a938681481 == 11)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(63);
	    }
	    if((((a1803458941 == 11) && (a23351479 == 12)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(64);
	    }
	    if((((a1716763601 == 4) && (a938681481 == 7)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(65);
	    }
	    if((((a23351479 == 12) && (a1047798024.equals("g"))) && (a1729378197 == 6))){
	    	cf = false;
	    	Errors.__VERIFIER_error(66);
	    }
	    if((((a520438996 == 6) && (a23351479 == 11)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(67);
	    }
	    if((((a68550605.equals("g")) && (a1920565083 == 14)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(68);
	    }
	    if((((a650861711.equals("g")) && (a1920565083 == 9)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(69);
	    }
	    if((((a520547452.equals("g")) && (a1477849038.equals("i"))) && (a1729378197 == 2))){
	    	cf = false;
	    	Errors.__VERIFIER_error(70);
	    }
	    if((((a650861711.equals("e")) && (a1920565083 == 9)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(71);
	    }
	    if((((a1075056448 == 11) && (a938681481 == 12)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(72);
	    }
	    if((((a198422080 == 6) && (a938681481 == 10)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(73);
	    }
	    if((((a948298434 == 8) && (a23351479 == 15)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(74);
	    }
	    if((((a853421711.equals("i")) && (a299375216 == 8)) && (a1729378197 == 8))){
	    	cf = false;
	    	Errors.__VERIFIER_error(75);
	    }
	    if((((a1716763601 == 10) && (a938681481 == 7)) && (a1729378197 == 1))){
	    	cf = false;
	    	Errors.__VERIFIER_error(76);
	    }
	    if((((a1105418891 == 9) && (a1920565083 == 15)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(77);
	    }
	    if((((a1114110175.equals("f")) && (a1477849038.equals("h"))) && (a1729378197 == 4))){
	    	cf = false;
	    	Errors.__VERIFIER_error(78);
	    }
	    if((((a1091978491 == 15) && (a123124249.equals("g"))) && (a1729378197 == 3))){
	    	cf = false;
	    	Errors.__VERIFIER_error(79);
	    }
	    if((((a541989745 == 4) && (a1477849038.equals("g"))) && (a1729378197 == 2))){
	    	cf = false;
	    	Errors.__VERIFIER_error(80);
	    }
	    if((((a853421711.equals("f")) && (a299375216 == 8)) && (a1729378197 == 8))){
	    	cf = false;
	    	Errors.__VERIFIER_error(81);
	    }
	    if((((a1583272058.equals("e")) && (a1047798024.equals("e"))) && (a1729378197 == 6))){
	    	cf = false;
	    	Errors.__VERIFIER_error(82);
	    }
	    if((((a1105727296.equals("g")) && (a299375216 == 5)) && (a1729378197 == 8))){
	    	cf = false;
	    	Errors.__VERIFIER_error(83);
	    }
	    if((((a1716858626.equals("i")) && (a1477849038.equals("e"))) && (a1729378197 == 4))){
	    	cf = false;
	    	Errors.__VERIFIER_error(84);
	    }
	    if((((a1105418891 == 7) && (a1920565083 == 15)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(85);
	    }
	    if((((a1091978491 == 8) && (a123124249.equals("g"))) && (a1729378197 == 3))){
	    	cf = false;
	    	Errors.__VERIFIER_error(86);
	    }
	    if((((a312388145 == 9) && (a1920565083 == 11)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(87);
	    }
	    if((((a1518235786 == 11) && (a1920565083 == 13)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(88);
	    }
	    if((((a1306585414.equals("e")) && (a299375216 == 7)) && (a1729378197 == 8))){
	    	cf = false;
	    	Errors.__VERIFIER_error(89);
	    }
	    if((((a1047798024.equals("e")) && (a299375216 == 2)) && (a1729378197 == 8))){
	    	cf = false;
	    	Errors.__VERIFIER_error(90);
	    }
	    if((((a310220227 == 8) && (a299375216 == 3)) && (a1729378197 == 8))){
	    	cf = false;
	    	Errors.__VERIFIER_error(91);
	    }
	    if((((a853421711.equals("h")) && (a299375216 == 8)) && (a1729378197 == 8))){
	    	cf = false;
	    	Errors.__VERIFIER_error(92);
	    }
	    if((((a312388145 == 12) && (a1920565083 == 11)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(93);
	    }
	    if((((a871304185 == 10) && (a23351479 == 14)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(94);
	    }
	    if((((a583157892.equals("g")) && (a23351479 == 16)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(95);
	    }
	    if((((a1668586383 == 9) && (a1920565083 == 8)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(96);
	    }
	    if((((a1105727296.equals("e")) && (a299375216 == 5)) && (a1729378197 == 8))){
	    	cf = false;
	    	Errors.__VERIFIER_error(97);
	    }
	    if((((a1518235786 == 12) && (a1920565083 == 13)) && (a1729378197 == 7))){
	    	cf = false;
	    	Errors.__VERIFIER_error(98);
	    }
	    if((((a123124249.equals("h")) && (a23351479 == 9)) && (a1729378197 == 5))){
	    	cf = false;
	    	Errors.__VERIFIER_error(99);
	    }
	}private  void calculateOutputm53(String input) {
    if((((a938681481 == 6) && ((cf && (input.equals("G"))) && (a1466114073.equals("e")))) && (a1729378197 == 1))) {
    	cf = false;
    	a847841994 = "g";
    	a1729378197 = 8;
    	a299375216 = 1; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm54(String input) {
    if((((((input.equals("B")) && cf) && (a1466114073.equals("f"))) && (a1729378197 == 1)) && (a938681481 == 6))) {
    	cf = false;
    	a911974320 = "h";
    	a938681481 = 9; 
    	System.out.println("X");
    } if(((a1729378197 == 1) && ((((input.equals("H")) && cf) && (a938681481 == 6)) && (a1466114073.equals("f"))))) {
    	cf = false;
    	 
    	System.out.println("T");
    } 
}
private  void calculateOutputm55(String input) {
    if(((a1466114073.equals("g")) && ((input.equals("C")) && ((a1729378197 == 1) && (cf && (a938681481 == 6)))))) {
    	cf = false;
    	a1477849038 = "g";
    	a1729378197 = 2;
    	a541989745 = 8; 
    	System.out.println("Q");
    } if((((input.equals("F")) && (((a938681481 == 6) && cf) && (a1466114073.equals("g")))) && (a1729378197 == 1))) {
    	cf = false;
    	a911974320 = "i";
    	a1047798024 = "i";
    	a1729378197 = 6; 
    	System.out.println("W");
    } if(((a1729378197 == 1) && ((a1466114073.equals("g")) && (((a938681481 == 6) && cf) && (input.equals("J")))))) {
    	cf = false;
    	a1729378197 = 7;
    	a650861711 = "f";
    	a1920565083 = 9; 
    	System.out.println("V");
    } 
}
private  void calculateOutputm56(String input) {
    if(((((a938681481 == 6) && ((a1466114073.equals("h")) && cf)) && (a1729378197 == 1)) && (input.equals("C")))) {
    	cf = false;
    	a938681481 = 11;
    	a1892947393 = 8; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm1(String input) {
    if((cf && (a1466114073.equals("e")))) {
    	calculateOutputm53(input);
    } 
    if(((a1466114073.equals("f")) && cf)) {
    	calculateOutputm54(input);
    } 
    if((cf && (a1466114073.equals("g")))) {
    	calculateOutputm55(input);
    } 
    if(((a1466114073.equals("h")) && cf)) {
    	calculateOutputm56(input);
    } 
}
private  void calculateOutputm60(String input) {
    if(((a938681481 == 7) && ((input.equals("A")) && (((a1716763601 == 5) && cf) && (a1729378197 == 1))))) {
    	cf = false;
    	a23351479 = 14;
    	a1729378197 = 5;
    	a871304185 = 4; 
    	System.out.println("T");
    } if(((a938681481 == 7) && ((input.equals("B")) && ((cf && (a1729378197 == 1)) && (a1716763601 == 5))))) {
    	cf = false;
    	a1920565083 = 13;
    	a1729378197 = 7;
    	a1518235786 = 6; 
    	System.out.println("Y");
    } if((((a1716763601 == 5) && ((input.equals("G")) && (cf && (a938681481 == 7)))) && (a1729378197 == 1))) {
    	cf = false;
    	a1937499914 = "i";
    	a938681481 = 13; 
    	System.out.println("Z");
    } if((((a1716763601 == 5) && ((cf && (input.equals("O"))) && (a1729378197 == 1))) && (a938681481 == 7))) {
    	cf = false;
    	a299375216 = 3;
    	a1729378197 = 8;
    	a310220227 = 11; 
    	System.out.println("T");
    } if(((((a938681481 == 7) && ((a1729378197 == 1) && cf)) && (input.equals("N"))) && (a1716763601 == 5))) {
    	cf = false;
    	a1729378197 = 8;
    	a1105727296 = "g";
    	a299375216 = 5; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm61(String input) {
    if((((input.equals("A")) && ((a1716763601 == 6) && ((a938681481 == 7) && cf))) && (a1729378197 == 1))) {
    	cf = false;
    	a938681481 = 10;
    	a198422080 = 12; 
    	System.out.println("T");
    } if(((a938681481 == 7) && ((a1716763601 == 6) && ((cf && (a1729378197 == 1)) && (input.equals("D")))))) {
    	cf = false;
    	a938681481 = 11;
    	a1892947393 = 8; 
    	System.out.println("W");
    } 
}
private  void calculateOutputm63(String input) {
    if(((a1716763601 == 9) && (((a1729378197 == 1) && (cf && (a938681481 == 7))) && (input.equals("B"))))) {
    	cf = false;
    	a145848903 = "h";
    	a123124249 = "e";
    	a1729378197 = 3; 
    	System.out.println("U");
    } if((((a1729378197 == 1) && ((a1716763601 == 9) && ((input.equals("H")) && cf))) && (a938681481 == 7))) {
    	cf = false;
    	a938681481 = 11;
    	a1892947393 = 8; 
    	System.out.println("Z");
    } if(((a1729378197 == 1) && (((input.equals("J")) && ((a938681481 == 7) && cf)) && (a1716763601 == 9)))) {
    	cf = false;
    	a938681481 = 10;
    	a198422080 = 10; 
    	System.out.println("R");
    } if(((((cf && (a938681481 == 7)) && (input.equals("L"))) && (a1716763601 == 9)) && (a1729378197 == 1))) {
    	cf = false;
    	a938681481 = 10;
    	a198422080 = 10; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm2(String input) {
    if((cf && (a1716763601 == 5))) {
    	calculateOutputm60(input);
    } 
    if((cf && (a1716763601 == 6))) {
    	calculateOutputm61(input);
    } 
    if((cf && (a1716763601 == 9))) {
    	calculateOutputm63(input);
    } 
}
private  void calculateOutputm65(String input) {
    if(((a938681481 == 8) && (((a1853964249 == 5) && ((a1729378197 == 1) && cf)) && (input.equals("B"))))) {
    	cf = false;
    	a123124249 = "i";
    	a366362113 = "i";
    	a1729378197 = 3; 
    	System.out.println("U");
    } if(((a938681481 == 8) && (((a1729378197 == 1) && ((input.equals("F")) && cf)) && (a1853964249 == 5)))) {
    	cf = false;
    	a123124249 = "e";
    	a145848903 = "h";
    	a1729378197 = 3; 
    	System.out.println("T");
    } if(((a938681481 == 8) && ((input.equals("L")) && (((a1729378197 == 1) && cf) && (a1853964249 == 5))))) {
    	cf = false;
    	a68550605 = "i";
    	a1729378197 = 7;
    	a1920565083 = 14; 
    	System.out.println("Y");
    } if(((((cf && (a1853964249 == 5)) && (input.equals("M"))) && (a1729378197 == 1)) && (a938681481 == 8))) {
    	cf = false;
    	a1729378197 = 7;
    	a68550605 = "i";
    	a1920565083 = 14; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm66(String input) {
    if(((a938681481 == 8) && (((cf && (input.equals("D"))) && (a1853964249 == 6)) && (a1729378197 == 1)))) {
    	cf = false;
    	a1584317767 = "g";
    	a1477849038 = "g";
    	a1729378197 = 4; 
    	System.out.println("R");
    } if((((((input.equals("J")) && cf) && (a1853964249 == 6)) && (a1729378197 == 1)) && (a938681481 == 8))) {
    	cf = false;
    	a1729378197 = 6;
    	a1047798024 = "g";
    	a23351479 = 15; 
    	System.out.println("Z");
    } if(((a938681481 == 8) && ((a1729378197 == 1) && (((a1853964249 == 6) && cf) && (input.equals("O")))))) {
    	cf = false;
    	a23351479 = 11;
    	a1729378197 = 5;
    	a520438996 = 10; 
    	System.out.println("Q");
    } if((((input.equals("N")) && (((a1853964249 == 6) && cf) && (a938681481 == 8))) && (a1729378197 == 1))) {
    	cf = false;
    	a1729378197 = 2;
    	a1477849038 = "g";
    	a541989745 = 9; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm67(String input) {
    if(((a1853964249 == 7) && (((cf && (input.equals("A"))) && (a1729378197 == 1)) && (a938681481 == 8)))) {
    	cf = false;
    	a1729378197 = 8;
    	a1306585414 = "g";
    	a299375216 = 7; 
    	System.out.println("S");
    } if(((input.equals("F")) && ((((a938681481 == 8) && cf) && (a1853964249 == 7)) && (a1729378197 == 1)))) {
    	cf = false;
    	a1729378197 = 5;
    	a23351479 = 14;
    	a871304185 = 8; 
    	System.out.println("S");
    } if(((a938681481 == 8) && (((a1853964249 == 7) && (cf && (input.equals("H")))) && (a1729378197 == 1)))) {
    	cf = false;
    	a938681481 = 11;
    	a1892947393 = 8; 
    	System.out.println("S");
    } if(((a1729378197 == 1) && ((a938681481 == 8) && (((a1853964249 == 7) && cf) && (input.equals("J")))))) {
    	cf = false;
    	a123124249 = "g";
    	a1729378197 = 3;
    	a1091978491 = 11; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm3(String input) {
    if(((a1853964249 == 5) && cf)) {
    	calculateOutputm65(input);
    } 
    if((cf && (a1853964249 == 6))) {
    	calculateOutputm66(input);
    } 
    if(((a1853964249 == 7) && cf)) {
    	calculateOutputm67(input);
    } 
}
private  void calculateOutputm71(String input) {
    if((((a911974320.equals("h")) && ((a1729378197 == 1) && (cf && (a938681481 == 9)))) && (input.equals("B")))) {
    	cf = false;
    	a1729378197 = 7;
    	a1920565083 = 13;
    	a1518235786 = 9; 
    	System.out.println("Y");
    } if(((a938681481 == 9) && ((input.equals("M")) && ((a1729378197 == 1) && ((a911974320.equals("h")) && cf))))) {
    	cf = false;
    	a1466114073 = "i";
    	a938681481 = 6; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm4(String input) {
    if((cf && (a911974320.equals("h")))) {
    	calculateOutputm71(input);
    } 
}
private  void calculateOutputm76(String input) {
    if(((a1729378197 == 1) && (((cf && (a938681481 == 10)) && (a198422080 == 10)) && (input.equals("C"))))) {
    	cf = false;
    	 
    	System.out.println("P");
    } if((((((a198422080 == 10) && cf) && (a938681481 == 10)) && (a1729378197 == 1)) && (input.equals("D")))) {
    	cf = false;
    	a1729378197 = 5;
    	a23351479 = 14;
    	a871304185 = 4; 
    	System.out.println("T");
    } if((((((input.equals("L")) && cf) && (a1729378197 == 1)) && (a198422080 == 10)) && (a938681481 == 10))) {
    	cf = false;
    	a23351479 = 14;
    	a1729378197 = 5;
    	a871304185 = 4; 
    	System.out.println("T");
    } if(((a1729378197 == 1) && ((((input.equals("O")) && cf) && (a938681481 == 10)) && (a198422080 == 10)))) {
    	cf = false;
    	a1937499914 = "f";
    	a938681481 = 13; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm77(String input) {
    if(((input.equals("F")) && ((((a198422080 == 11) && cf) && (a938681481 == 10)) && (a1729378197 == 1)))) {
    	cf = false;
    	a750845785 = "i";
    	a1729378197 = 7;
    	a1920565083 = 12; 
    	System.out.println("R");
    } if((((((a938681481 == 10) && cf) && (input.equals("J"))) && (a1729378197 == 1)) && (a198422080 == 11))) {
    	cf = false;
    	a123124249 = "i";
    	a366362113 = "h";
    	a1729378197 = 3; 
    	System.out.println("R");
    } 
}
private  void calculateOutputm78(String input) {
    if((((a1729378197 == 1) && (((a198422080 == 12) && cf) && (input.equals("A")))) && (a938681481 == 10))) {
    	cf = false;
    	 
    	System.out.println("Q");
    } if(((a198422080 == 12) && ((a1729378197 == 1) && ((cf && (input.equals("B"))) && (a938681481 == 10))))) {
    	cf = false;
    	 
    	System.out.println("Z");
    } if(((a198422080 == 12) && (((a938681481 == 10) && ((input.equals("C")) && cf)) && (a1729378197 == 1)))) {
    	cf = false;
    	a1937499914 = "f";
    	a938681481 = 13; 
    	System.out.println("W");
    } if(((a198422080 == 12) && ((((a938681481 == 10) && cf) && (a1729378197 == 1)) && (input.equals("H"))))) {
    	cf = false;
    	a1937499914 = "f";
    	a938681481 = 13; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm5(String input) {
    if((cf && (a198422080 == 10))) {
    	calculateOutputm76(input);
    } 
    if(((a198422080 == 11) && cf)) {
    	calculateOutputm77(input);
    } 
    if(((a198422080 == 12) && cf)) {
    	calculateOutputm78(input);
    } 
}
private  void calculateOutputm79(String input) {
    if(((a1892947393 == 5) && ((input.equals("B")) && ((a1729378197 == 1) && (cf && (a938681481 == 11)))))) {
    	cf = false;
    	a1729378197 = 8;
    	a299375216 = 3;
    	a310220227 = 9; 
    	System.out.println("T");
    } if(((input.equals("F")) && (((a1892947393 == 5) && ((a1729378197 == 1) && cf)) && (a938681481 == 11)))) {
    	cf = false;
    	a750845785 = "f";
    	a1729378197 = 7;
    	a1920565083 = 12; 
    	System.out.println("P");
    } if((((((a1892947393 == 5) && cf) && (input.equals("K"))) && (a938681481 == 11)) && (a1729378197 == 1))) {
    	cf = false;
    	a1477849038 = "g";
    	a1584317767 = "i";
    	a1729378197 = 4; 
    	System.out.println("T");
    } if(((a1892947393 == 5) && ((a1729378197 == 1) && ((cf && (input.equals("L"))) && (a938681481 == 11))))) {
    	cf = false;
    	a1729378197 = 8;
    	a299375216 = 4;
    	a1105418891 = 11; 
    	System.out.println("W");
    } 
}
private  void calculateOutputm80(String input) {
    if(((a1892947393 == 6) && ((a938681481 == 11) && (((input.equals("A")) && cf) && (a1729378197 == 1))))) {
    	cf = false;
    	a1466114073 = "g";
    	a938681481 = 6; 
    	System.out.println("T");
    } if(((a1729378197 == 1) && ((a938681481 == 11) && ((a1892947393 == 6) && (cf && (input.equals("K"))))))) {
    	cf = false;
    	a938681481 = 7;
    	a1716763601 = 9; 
    	System.out.println("Z");
    } if(((a1729378197 == 1) && ((input.equals("L")) && ((a1892947393 == 6) && (cf && (a938681481 == 11)))))) {
    	cf = false;
    	a1047798024 = "h";
    	a274626616 = "i";
    	a1729378197 = 6; 
    	System.out.println("R");
    } if(((a938681481 == 11) && ((input.equals("M")) && (((a1892947393 == 6) && cf) && (a1729378197 == 1))))) {
    	cf = false;
    	a1729378197 = 7;
    	a750845785 = "e";
    	a1920565083 = 12; 
    	System.out.println("R");
    } if(((((a1892947393 == 6) && (cf && (a938681481 == 11))) && (input.equals("G"))) && (a1729378197 == 1))) {
    	cf = false;
    	a938681481 = 7;
    	a1716763601 = 7; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm81(String input) {
    if((((((input.equals("K")) && cf) && (a1892947393 == 8)) && (a938681481 == 11)) && (a1729378197 == 1))) {
    	cf = false;
    	a938681481 = 7;
    	a1716763601 = 5; 
    	System.out.println("Y");
    } if((((a938681481 == 11) && ((input.equals("M")) && (cf && (a1729378197 == 1)))) && (a1892947393 == 8))) {
    	cf = false;
    	a1729378197 = 7;
    	a1920565083 = 8;
    	a1668586383 = 2; 
    	System.out.println("V");
    } 
}
private  void calculateOutputm82(String input) {
    if((((((a1892947393 == 9) && cf) && (a938681481 == 11)) && (a1729378197 == 1)) && (input.equals("A")))) {
    	cf = false;
    	a123124249 = "e";
    	a145848903 = "h";
    	a1729378197 = 3; 
    	System.out.println("S");
    } if(((a1892947393 == 9) && ((((a938681481 == 11) && cf) && (input.equals("H"))) && (a1729378197 == 1)))) {
    	cf = false;
    	a299375216 = 3;
    	a1729378197 = 8;
    	a310220227 = 7; 
    	System.out.println("Y");
    } if((((((input.equals("M")) && cf) && (a938681481 == 11)) && (a1892947393 == 9)) && (a1729378197 == 1))) {
    	cf = false;
    	a123124249 = "f";
    	a1584317767 = "h";
    	a1729378197 = 3; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm83(String input) {
    if(((a1892947393 == 10) && ((a1729378197 == 1) && (((input.equals("A")) && cf) && (a938681481 == 11))))) {
    	cf = false;
    	a123124249 = "h";
    	a1729378197 = 3;
    	a198422080 = 11; 
    	System.out.println("S");
    } if(((input.equals("C")) && (((cf && (a1892947393 == 10)) && (a1729378197 == 1)) && (a938681481 == 11)))) {
    	cf = false;
    	a1477849038 = "f";
    	a625366011 = "f";
    	a1729378197 = 2; 
    	System.out.println("T");
    } if(((a1892947393 == 10) && ((((input.equals("D")) && cf) && (a1729378197 == 1)) && (a938681481 == 11)))) {
    	cf = false;
    	a1729378197 = 3;
    	a123124249 = "g";
    	a1091978491 = 9; 
    	System.out.println("X");
    } if(((a1729378197 == 1) && ((input.equals("F")) && ((a1892947393 == 10) && ((a938681481 == 11) && cf))))) {
    	cf = false;
    	a1729378197 = 5;
    	a23351479 = 15;
    	a948298434 = 13; 
    	System.out.println("V");
    } 
}
private  void calculateOutputm6(String input) {
    if((cf && (a1892947393 == 5))) {
    	calculateOutputm79(input);
    } 
    if((cf && (a1892947393 == 6))) {
    	calculateOutputm80(input);
    } 
    if(((a1892947393 == 8) && cf)) {
    	calculateOutputm81(input);
    } 
    if(((a1892947393 == 9) && cf)) {
    	calculateOutputm82(input);
    } 
    if(((a1892947393 == 10) && cf)) {
    	calculateOutputm83(input);
    } 
}
private  void calculateOutputm86(String input) {
    if((((a938681481 == 12) && ((a1729378197 == 1) && (cf && (input.equals("C"))))) && (a1075056448 == 5))) {
    	cf = false;
    	a911974320 = "f";
    	a1047798024 = "i";
    	a1729378197 = 6; 
    	System.out.println("S");
    } if(((input.equals("L")) && ((((a1075056448 == 5) && cf) && (a1729378197 == 1)) && (a938681481 == 12)))) {
    	cf = false;
    	a911974320 = "g";
    	a1047798024 = "i";
    	a1729378197 = 6; 
    	System.out.println("Q");
    } if((((a1075056448 == 5) && ((a938681481 == 12) && (cf && (a1729378197 == 1)))) && (input.equals("D")))) {
    	cf = false;
    	a123124249 = "h";
    	a1729378197 = 3;
    	a198422080 = 10; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm87(String input) {
    if(((a1075056448 == 6) && ((a938681481 == 12) && ((a1729378197 == 1) && ((input.equals("A")) && cf))))) {
    	cf = false;
    	a1920565083 = 13;
    	a1729378197 = 7;
    	a1518235786 = 10; 
    	System.out.println("S");
    } if(((input.equals("B")) && ((a938681481 == 12) && ((a1729378197 == 1) && ((a1075056448 == 6) && cf))))) {
    	cf = false;
    	a650861711 = "f";
    	a1729378197 = 7;
    	a1920565083 = 9; 
    	System.out.println("S");
    } if(((a938681481 == 12) && ((a1729378197 == 1) && ((cf && (input.equals("J"))) && (a1075056448 == 6))))) {
    	cf = false;
    	a938681481 = 10;
    	a198422080 = 12; 
    	System.out.println("S");
    } if((((((a938681481 == 12) && cf) && (input.equals("O"))) && (a1075056448 == 6)) && (a1729378197 == 1))) {
    	cf = false;
    	a1729378197 = 8;
    	a1039409491 = "g";
    	a299375216 = 6; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm88(String input) {
    if((((input.equals("C")) && ((a1729378197 == 1) && ((a1075056448 == 7) && cf))) && (a938681481 == 12))) {
    	cf = false;
    	a1477849038 = "h";
    	a1114110175 = "i";
    	a1729378197 = 4; 
    	System.out.println("Z");
    } if(((((a1729378197 == 1) && (cf && (input.equals("O")))) && (a938681481 == 12)) && (a1075056448 == 7))) {
    	cf = false;
    	a23351479 = 10;
    	a1729378197 = 5;
    	a37252965 = 15; 
    	System.out.println("X");
    } 
}
private  void calculateOutputm89(String input) {
    if(((input.equals("F")) && (((a1075056448 == 8) && (cf && (a1729378197 == 1))) && (a938681481 == 12)))) {
    	cf = false;
    	a938681481 = 10;
    	a198422080 = 12; 
    	System.out.println("R");
    } if(((input.equals("H")) && ((a938681481 == 12) && ((cf && (a1075056448 == 8)) && (a1729378197 == 1))))) {
    	cf = false;
    	a1729378197 = 7;
    	a1920565083 = 13;
    	a1518235786 = 9; 
    	System.out.println("Q");
    } if(((((a1075056448 == 8) && ((a938681481 == 12) && cf)) && (input.equals("J"))) && (a1729378197 == 1))) {
    	cf = false;
    	a1477849038 = "e";
    	a1716858626 = "e";
    	a1729378197 = 4; 
    	System.out.println("X");
    } if((((a1075056448 == 8) && ((a1729378197 == 1) && (cf && (input.equals("M"))))) && (a938681481 == 12))) {
    	cf = false;
    	a938681481 = 11;
    	a1892947393 = 8; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm92(String input) {
    if(((a1075056448 == 12) && ((((input.equals("K")) && cf) && (a1729378197 == 1)) && (a938681481 == 12)))) {
    	cf = false;
    	a648437939 = "f";
    	a1477849038 = "h";
    	a1729378197 = 2; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm7(String input) {
    if(((a1075056448 == 5) && cf)) {
    	calculateOutputm86(input);
    } 
    if((cf && (a1075056448 == 6))) {
    	calculateOutputm87(input);
    } 
    if(((a1075056448 == 7) && cf)) {
    	calculateOutputm88(input);
    } 
    if((cf && (a1075056448 == 8))) {
    	calculateOutputm89(input);
    } 
    if((cf && (a1075056448 == 12))) {
    	calculateOutputm92(input);
    } 
}
private  void calculateOutputm93(String input) {
    if(((a938681481 == 13) && (((a1937499914.equals("e")) && (cf && (a1729378197 == 1))) && (input.equals("A"))))) {
    	cf = false;
    	a1477849038 = "e";
    	a1716858626 = "e";
    	a1729378197 = 4; 
    	System.out.println("S");
    } if((((input.equals("F")) && ((a1729378197 == 1) && ((a938681481 == 13) && cf))) && (a1937499914.equals("e")))) {
    	cf = false;
    	a1729378197 = 8;
    	a299375216 = 3;
    	a310220227 = 9; 
    	System.out.println("Y");
    } if(((input.equals("H")) && (((a1937499914.equals("e")) && ((a1729378197 == 1) && cf)) && (a938681481 == 13)))) {
    	cf = false;
    	a938681481 = 10;
    	a198422080 = 10; 
    	System.out.println("Y");
    } if(((((cf && (a938681481 == 13)) && (input.equals("O"))) && (a1937499914.equals("e"))) && (a1729378197 == 1))) {
    	cf = false;
    	a938681481 = 12;
    	a1075056448 = 7; 
    	System.out.println("R");
    } 
}
private  void calculateOutputm94(String input) {
    if((((a1937499914.equals("f")) && ((a1729378197 == 1) && ((input.equals("B")) && cf))) && (a938681481 == 13))) {
    	cf = false;
    	a123124249 = "i";
    	a366362113 = "e";
    	a1729378197 = 3; 
    	System.out.println("W");
    } if((((((a1729378197 == 1) && cf) && (a1937499914.equals("f"))) && (input.equals("J"))) && (a938681481 == 13))) {
    	cf = false;
    	a938681481 = 7;
    	a1716763601 = 5; 
    	System.out.println("Y");
    } if(((a938681481 == 13) && ((input.equals("K")) && (((a1729378197 == 1) && cf) && (a1937499914.equals("f")))))) {
    	cf = false;
    	a1729378197 = 7;
    	a1245641101 = "h";
    	a1920565083 = 10; 
    	System.out.println("W");
    } if((((a1729378197 == 1) && ((a938681481 == 13) && ((a1937499914.equals("f")) && cf))) && (input.equals("O")))) {
    	cf = false;
    	a1920565083 = 11;
    	a1729378197 = 7;
    	a312388145 = 6; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm95(String input) {
    if(((a1937499914.equals("i")) && ((a938681481 == 13) && ((cf && (input.equals("D"))) && (a1729378197 == 1))))) {
    	cf = false;
    	a648437939 = "h";
    	a1477849038 = "h";
    	a1729378197 = 2; 
    	System.out.println("T");
    } if(((((a1937499914.equals("i")) && ((a938681481 == 13) && cf)) && (a1729378197 == 1)) && (input.equals("F")))) {
    	cf = false;
    	a1729378197 = 5;
    	a23351479 = 14;
    	a871304185 = 3; 
    	System.out.println("P");
    } if(((a1937499914.equals("i")) && (((a1729378197 == 1) && ((a938681481 == 13) && cf)) && (input.equals("G"))))) {
    	cf = false;
    	a1729378197 = 5;
    	a23351479 = 10;
    	a37252965 = 15; 
    	System.out.println("X");
    } if(((a1729378197 == 1) && ((input.equals("H")) && ((a938681481 == 13) && (cf && (a1937499914.equals("i"))))))) {
    	cf = false;
    	a1477849038 = "f";
    	a625366011 = "e";
    	a1729378197 = 2; 
    	System.out.println("W");
    } if(((a1937499914.equals("i")) && ((a1729378197 == 1) && ((cf && (a938681481 == 13)) && (input.equals("A")))))) {
    	cf = false;
    	a938681481 = 8;
    	a1853964249 = 8; 
    	System.out.println("P");
    } 
}
private  void calculateOutputm8(String input) {
    if((cf && (a1937499914.equals("e")))) {
    	calculateOutputm93(input);
    } 
    if((cf && (a1937499914.equals("f")))) {
    	calculateOutputm94(input);
    } 
    if(((a1937499914.equals("i")) && cf)) {
    	calculateOutputm95(input);
    } 
}
private  void calculateOutputm96(String input) {
    if(((a1477849038.equals("e")) && ((a674877.equals("e")) && ((a1729378197 == 2) && ((input.equals("C")) && cf))))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 7;
    	a1716763601 = 5; 
    	System.out.println("Y");
    } if((((a1729378197 == 2) && ((cf && (a674877.equals("e"))) && (input.equals("J")))) && (a1477849038.equals("e")))) {
    	cf = false;
    	a1729378197 = 1;
    	a1937499914 = "i";
    	a938681481 = 13; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm97(String input) {
    if((((a1477849038.equals("e")) && ((a1729378197 == 2) && ((input.equals("J")) && cf))) && (a674877.equals("f")))) {
    	cf = false;
    	a1477849038 = "h";
    	a1114110175 = "i";
    	a1729378197 = 4; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm99(String input) {
    if(((input.equals("A")) && ((a1477849038.equals("e")) && ((a674877.equals("i")) && (cf && (a1729378197 == 2)))))) {
    	cf = false;
    	a1729378197 = 8;
    	a1306585414 = "g";
    	a299375216 = 7; 
    	System.out.println("T");
    } if(((a674877.equals("i")) && ((input.equals("G")) && ((a1729378197 == 2) && ((a1477849038.equals("e")) && cf))))) {
    	cf = false;
    	a1477849038 = "g";
    	a541989745 = 8; 
    	System.out.println("Q");
    } if(((input.equals("L")) && (((a1477849038.equals("e")) && (cf && (a1729378197 == 2))) && (a674877.equals("i"))))) {
    	cf = false;
    	a1729378197 = 8;
    	a299375216 = 3;
    	a310220227 = 10; 
    	System.out.println("P");
    } 
}
private  void calculateOutputm9(String input) {
    if((cf && (a674877.equals("e")))) {
    	calculateOutputm96(input);
    } 
    if((cf && (a674877.equals("f")))) {
    	calculateOutputm97(input);
    } 
    if((cf && (a674877.equals("i")))) {
    	calculateOutputm99(input);
    } 
}
private  void calculateOutputm100(String input) {
    if(((a1729378197 == 2) && ((input.equals("A")) && ((a1477849038.equals("f")) && ((a625366011.equals("e")) && cf))))) {
    	cf = false;
    	a911974320 = "i";
    	a1047798024 = "i";
    	a1729378197 = 6; 
    	System.out.println("U");
    } if(((a1477849038.equals("f")) && (((a1729378197 == 2) && (cf && (input.equals("C")))) && (a625366011.equals("e"))))) {
    	cf = false;
    	a1729378197 = 7;
    	a1920565083 = 13;
    	a1518235786 = 10; 
    	System.out.println("P");
    } if((((a1477849038.equals("f")) && ((input.equals("F")) && ((a1729378197 == 2) && cf))) && (a625366011.equals("e")))) {
    	cf = false;
    	a1729378197 = 5;
    	a23351479 = 14;
    	a871304185 = 8; 
    	System.out.println("V");
    } if(((a625366011.equals("e")) && ((input.equals("J")) && ((a1477849038.equals("f")) && (cf && (a1729378197 == 2)))))) {
    	cf = false;
    	a299375216 = 3;
    	a1729378197 = 8;
    	a310220227 = 10; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm101(String input) {
    if(((a625366011.equals("f")) && (((a1729378197 == 2) && ((a1477849038.equals("f")) && cf)) && (input.equals("A"))))) {
    	cf = false;
    	a23351479 = 10;
    	a1729378197 = 5;
    	a37252965 = 9; 
    	System.out.println("X");
    } if(((((a625366011.equals("f")) && (cf && (input.equals("F")))) && (a1729378197 == 2)) && (a1477849038.equals("f")))) {
    	cf = false;
    	a123124249 = "f";
    	a1584317767 = "i";
    	a1729378197 = 3; 
    	System.out.println("W");
    } if(((a625366011.equals("f")) && ((a1477849038.equals("f")) && ((cf && (a1729378197 == 2)) && (input.equals("O")))))) {
    	cf = false;
    	a911974320 = "i";
    	a1047798024 = "i";
    	a1729378197 = 6; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm102(String input) {
    if(((((a1729378197 == 2) && (cf && (a625366011.equals("h")))) && (a1477849038.equals("f"))) && (input.equals("D")))) {
    	cf = false;
    	a1729378197 = 5;
    	a23351479 = 11;
    	a520438996 = 8; 
    	System.out.println("Y");
    } if(((((cf && (a625366011.equals("h"))) && (a1477849038.equals("f"))) && (input.equals("H"))) && (a1729378197 == 2))) {
    	cf = false;
    	a123124249 = "f";
    	a1729378197 = 5;
    	a23351479 = 9; 
    	System.out.println("T");
    } if((((a1477849038.equals("f")) && (((a1729378197 == 2) && cf) && (a625366011.equals("h")))) && (input.equals("M")))) {
    	cf = false;
    	a23351479 = 12;
    	a1729378197 = 5;
    	a1803458941 = 15; 
    	System.out.println("U");
    } if((((((a1729378197 == 2) && cf) && (input.equals("O"))) && (a1477849038.equals("f"))) && (a625366011.equals("h")))) {
    	cf = false;
    	a1477849038 = "i";
    	a1729378197 = 4;
    	a50296898 = 13; 
    	System.out.println("R");
    } 
}
private  void calculateOutputm103(String input) {
    if(((((a1477849038.equals("f")) && ((a625366011.equals("i")) && cf)) && (input.equals("H"))) && (a1729378197 == 2))) {
    	cf = false;
    	a1729378197 = 8;
    	a1039409491 = "e";
    	a299375216 = 6; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm10(String input) {
    if(((a625366011.equals("e")) && cf)) {
    	calculateOutputm100(input);
    } 
    if((cf && (a625366011.equals("f")))) {
    	calculateOutputm101(input);
    } 
    if(((a625366011.equals("h")) && cf)) {
    	calculateOutputm102(input);
    } 
    if(((a625366011.equals("i")) && cf)) {
    	calculateOutputm103(input);
    } 
}
private  void calculateOutputm104(String input) {
    if(((input.equals("H")) && (((cf && (a541989745 == 3)) && (a1477849038.equals("g"))) && (a1729378197 == 2)))) {
    	cf = false;
    	a366362113 = "h";
    	a123124249 = "i";
    	a1729378197 = 3; 
    	System.out.println("P");
    } if((((a1477849038.equals("g")) && ((input.equals("O")) && ((a1729378197 == 2) && cf))) && (a541989745 == 3))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 10;
    	a198422080 = 10; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm106(String input) {
    if((((input.equals("C")) && ((a541989745 == 5) && (cf && (a1477849038.equals("g"))))) && (a1729378197 == 2))) {
    	cf = false;
    	a299375216 = 4;
    	a1729378197 = 8;
    	a1105418891 = 11; 
    	System.out.println("X");
    } if((((a541989745 == 5) && (((a1477849038.equals("g")) && cf) && (a1729378197 == 2))) && (input.equals("H")))) {
    	cf = false;
    	a541989745 = 6; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm108(String input) {
    if(((((a1477849038.equals("g")) && ((a1729378197 == 2) && cf)) && (input.equals("A"))) && (a541989745 == 7))) {
    	cf = false;
    	a1729378197 = 1;
    	a1466114073 = "e";
    	a938681481 = 6; 
    	System.out.println("P");
    } if(((a1477849038.equals("g")) && ((a1729378197 == 2) && ((cf && (a541989745 == 7)) && (input.equals("N")))))) {
    	cf = false;
    	a1047798024 = "e";
    	a1583272058 = "i";
    	a1729378197 = 6; 
    	System.out.println("P");
    } 
}
private  void calculateOutputm109(String input) {
    if((((a1729378197 == 2) && ((a1477849038.equals("g")) && ((a541989745 == 8) && cf))) && (input.equals("B")))) {
    	cf = false;
    	 
    	System.out.println("U");
    } if(((a541989745 == 8) && ((a1477849038.equals("g")) && (((input.equals("G")) && cf) && (a1729378197 == 2))))) {
    	cf = false;
    	a1729378197 = 5;
    	a23351479 = 14;
    	a871304185 = 4; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm111(String input) {
    if(((input.equals("B")) && (((a541989745 == 10) && (cf && (a1477849038.equals("g")))) && (a1729378197 == 2)))) {
    	cf = false;
    	a1729378197 = 3;
    	a123124249 = "h";
    	a198422080 = 6; 
    	System.out.println("T");
    } if(((((input.equals("D")) && (cf && (a1729378197 == 2))) && (a541989745 == 10)) && (a1477849038.equals("g")))) {
    	cf = false;
    	a1729378197 = 7;
    	a1245641101 = "i";
    	a1920565083 = 10; 
    	System.out.println("Q");
    } if((((a1729378197 == 2) && ((input.equals("G")) && (cf && (a541989745 == 10)))) && (a1477849038.equals("g")))) {
    	cf = false;
    	a1729378197 = 8;
    	a299375216 = 4;
    	a1105418891 = 12; 
    	System.out.println("X");
    } if(((((cf && (a1477849038.equals("g"))) && (input.equals("J"))) && (a541989745 == 10)) && (a1729378197 == 2))) {
    	cf = false;
    	a123124249 = "g";
    	a1729378197 = 5;
    	a23351479 = 9; 
    	System.out.println("S");
    } if((((input.equals("C")) && ((cf && (a1477849038.equals("g"))) && (a1729378197 == 2))) && (a541989745 == 10))) {
    	cf = false;
    	a853421711 = "f";
    	a1729378197 = 8;
    	a299375216 = 8; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm11(String input) {
    if(((a541989745 == 3) && cf)) {
    	calculateOutputm104(input);
    } 
    if(((a541989745 == 5) && cf)) {
    	calculateOutputm106(input);
    } 
    if((cf && (a541989745 == 7))) {
    	calculateOutputm108(input);
    } 
    if(((a541989745 == 8) && cf)) {
    	calculateOutputm109(input);
    } 
    if(((a541989745 == 10) && cf)) {
    	calculateOutputm111(input);
    } 
}
private  void calculateOutputm113(String input) {
    if((((a1729378197 == 2) && ((a1477849038.equals("h")) && (cf && (a648437939.equals("f"))))) && (input.equals("C")))) {
    	cf = false;
    	a750845785 = "f";
    	a1729378197 = 7;
    	a1920565083 = 12; 
    	System.out.println("Q");
    } if((((a648437939.equals("f")) && (((a1477849038.equals("h")) && cf) && (a1729378197 == 2))) && (input.equals("J")))) {
    	cf = false;
    	a68550605 = "f";
    	a1729378197 = 7;
    	a1920565083 = 14; 
    	System.out.println("V");
    } if(((((cf && (input.equals("O"))) && (a648437939.equals("f"))) && (a1729378197 == 2)) && (a1477849038.equals("h")))) {
    	cf = false;
    	a299375216 = 3;
    	a1729378197 = 8;
    	a310220227 = 7; 
    	System.out.println("V");
    } 
}
private  void calculateOutputm114(String input) {
    if(((input.equals("B")) && ((a648437939.equals("g")) && ((a1477849038.equals("h")) && (cf && (a1729378197 == 2)))))) {
    	cf = false;
    	a1477849038 = "g";
    	a1584317767 = "i";
    	a1729378197 = 4; 
    	System.out.println("V");
    } if((((((a648437939.equals("g")) && cf) && (input.equals("L"))) && (a1477849038.equals("h"))) && (a1729378197 == 2))) {
    	cf = false;
    	a1047798024 = "g";
    	a1729378197 = 6;
    	a23351479 = 13; 
    	System.out.println("Z");
    } if(((input.equals("M")) && ((a648437939.equals("g")) && (((a1477849038.equals("h")) && cf) && (a1729378197 == 2))))) {
    	cf = false;
    	a1729378197 = 8;
    	a299375216 = 3;
    	a310220227 = 9; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm115(String input) {
    if(((((a1477849038.equals("h")) && ((a1729378197 == 2) && cf)) && (input.equals("A"))) && (a648437939.equals("h")))) {
    	cf = false;
    	a1047798024 = "g";
    	a1729378197 = 6;
    	a23351479 = 14; 
    	System.out.println("S");
    } if((((a1477849038.equals("h")) && (((a1729378197 == 2) && cf) && (a648437939.equals("h")))) && (input.equals("C")))) {
    	cf = false;
    	a1477849038 = "e";
    	a674877 = "e"; 
    	System.out.println("Z");
    } if(((a648437939.equals("h")) && ((((a1729378197 == 2) && cf) && (input.equals("D"))) && (a1477849038.equals("h"))))) {
    	cf = false;
    	a123124249 = "i";
    	a366362113 = "h";
    	a1729378197 = 3; 
    	System.out.println("S");
    } if(((a1729378197 == 2) && ((a648437939.equals("h")) && ((cf && (a1477849038.equals("h"))) && (input.equals("L")))))) {
    	cf = false;
    	a1477849038 = "e";
    	a674877 = "f"; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm116(String input) {
    if(((((cf && (a1477849038.equals("h"))) && (a1729378197 == 2)) && (input.equals("A"))) && (a648437939.equals("i")))) {
    	cf = false;
    	 
    	System.out.println("W");
    } if(((a1729378197 == 2) && ((input.equals("G")) && ((cf && (a1477849038.equals("h"))) && (a648437939.equals("i")))))) {
    	cf = false;
    	a1477849038 = "e";
    	a674877 = "e"; 
    	System.out.println("W");
    } if(((a1477849038.equals("h")) && ((((a648437939.equals("i")) && cf) && (input.equals("H"))) && (a1729378197 == 2)))) {
    	cf = false;
    	 
    	System.out.println("Q");
    } if(((((a1729378197 == 2) && ((a1477849038.equals("h")) && cf)) && (a648437939.equals("i"))) && (input.equals("M")))) {
    	cf = false;
    	a299375216 = 3;
    	a1729378197 = 8;
    	a310220227 = 9; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm12(String input) {
    if((cf && (a648437939.equals("f")))) {
    	calculateOutputm113(input);
    } 
    if((cf && (a648437939.equals("g")))) {
    	calculateOutputm114(input);
    } 
    if((cf && (a648437939.equals("h")))) {
    	calculateOutputm115(input);
    } 
    if((cf && (a648437939.equals("i")))) {
    	calculateOutputm116(input);
    } 
}
private  void calculateOutputm122(String input) {
    if(((((input.equals("H")) && ((a1729378197 == 3) && cf)) && (a145848903.equals("h"))) && (a123124249.equals("e")))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 7;
    	a1716763601 = 5; 
    	System.out.println("Y");
    } if(((input.equals("J")) && ((a1729378197 == 3) && ((cf && (a123124249.equals("e"))) && (a145848903.equals("h")))))) {
    	cf = false;
    	a1920565083 = 13;
    	a1729378197 = 7;
    	a1518235786 = 6; 
    	System.out.println("Y");
    } if(((a1729378197 == 3) && ((((input.equals("K")) && cf) && (a123124249.equals("e"))) && (a145848903.equals("h"))))) {
    	cf = false;
    	a1477849038 = "h";
    	a1114110175 = "i";
    	a1729378197 = 4; 
    	System.out.println("Z");
    } if((((input.equals("M")) && (((a145848903.equals("h")) && cf) && (a1729378197 == 3))) && (a123124249.equals("e")))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 7;
    	a1716763601 = 5; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm14(String input) {
    if((cf && (a145848903.equals("h")))) {
    	calculateOutputm122(input);
    } 
}
private  void calculateOutputm127(String input) {
    if(((((a1584317767.equals("h")) && ((a123124249.equals("f")) && cf)) && (a1729378197 == 3)) && (input.equals("A")))) {
    	cf = false;
    	 
    	System.out.println("S");
    } if(((a1729378197 == 3) && (((cf && (a123124249.equals("f"))) && (a1584317767.equals("h"))) && (input.equals("H"))))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 7;
    	a1716763601 = 5; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm128(String input) {
    if(((((cf && (a1729378197 == 3)) && (input.equals("O"))) && (a1584317767.equals("i"))) && (a123124249.equals("f")))) {
    	cf = false;
    	a1047798024 = "g";
    	a1729378197 = 8;
    	a299375216 = 2; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm15(String input) {
    if((cf && (a1584317767.equals("h")))) {
    	calculateOutputm127(input);
    } 
    if(((a1584317767.equals("i")) && cf)) {
    	calculateOutputm128(input);
    } 
}
private  void calculateOutputm130(String input) {
    if((((input.equals("A")) && ((a123124249.equals("g")) && (cf && (a1729378197 == 3)))) && (a1091978491 == 9))) {
    	cf = false;
    	a123124249 = "i";
    	a366362113 = "h"; 
    	System.out.println("T");
    } if(((((a1729378197 == 3) && ((a1091978491 == 9) && cf)) && (input.equals("J"))) && (a123124249.equals("g")))) {
    	cf = false;
    	a1477849038 = "g";
    	a1584317767 = "i";
    	a1729378197 = 4; 
    	System.out.println("Y");
    } if((((a1729378197 == 3) && (((input.equals("O")) && cf) && (a1091978491 == 9))) && (a123124249.equals("g")))) {
    	cf = false;
    	a1729378197 = 7;
    	a68550605 = "i";
    	a1920565083 = 14; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm132(String input) {
    if((((a123124249.equals("g")) && (((a1091978491 == 11) && cf) && (a1729378197 == 3))) && (input.equals("A")))) {
    	cf = false;
    	a1245641101 = "i";
    	a1729378197 = 7;
    	a1920565083 = 10; 
    	System.out.println("Q");
    } if((((a1091978491 == 11) && ((a123124249.equals("g")) && ((input.equals("B")) && cf))) && (a1729378197 == 3))) {
    	cf = false;
    	 
    	System.out.println("Y");
    } if((((((a1729378197 == 3) && cf) && (input.equals("K"))) && (a1091978491 == 11)) && (a123124249.equals("g")))) {
    	cf = false;
    	a1729378197 = 2;
    	a1477849038 = "g";
    	a541989745 = 10; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm16(String input) {
    if((cf && (a1091978491 == 9))) {
    	calculateOutputm130(input);
    } 
    if(((a1091978491 == 11) && cf)) {
    	calculateOutputm132(input);
    } 
}
private  void calculateOutputm136(String input) {
    if(((a123124249.equals("h")) && (((a1729378197 == 3) && ((a198422080 == 6) && cf)) && (input.equals("G"))))) {
    	cf = false;
    	a1245641101 = "f";
    	a1729378197 = 7;
    	a1920565083 = 10; 
    	System.out.println("Q");
    } if((((((a123124249.equals("h")) && cf) && (input.equals("M"))) && (a198422080 == 6)) && (a1729378197 == 3))) {
    	cf = false;
    	a1937499914 = "e";
    	a1729378197 = 1;
    	a938681481 = 13; 
    	System.out.println("W");
    } 
}
private  void calculateOutputm137(String input) {
    if(((a123124249.equals("h")) && (((cf && (a1729378197 == 3)) && (input.equals("F"))) && (a198422080 == 7)))) {
    	cf = false;
    	a1729378197 = 5;
    	a123124249 = "e";
    	a23351479 = 9; 
    	System.out.println("T");
    } if(((a1729378197 == 3) && (((cf && (input.equals("J"))) && (a123124249.equals("h"))) && (a198422080 == 7)))) {
    	cf = false;
    	a1466114073 = "f";
    	a1729378197 = 1;
    	a938681481 = 6; 
    	System.out.println("P");
    } if((((((input.equals("K")) && cf) && (a1729378197 == 3)) && (a198422080 == 7)) && (a123124249.equals("h")))) {
    	cf = false;
    	a1729378197 = 8;
    	a299375216 = 4;
    	a1105418891 = 7; 
    	System.out.println("V");
    } if((((a1729378197 == 3) && ((a123124249.equals("h")) && (cf && (a198422080 == 7)))) && (input.equals("M")))) {
    	cf = false;
    	a1729378197 = 1;
    	a911974320 = "f";
    	a938681481 = 9; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm140(String input) {
    if((((((a198422080 == 11) && cf) && (a1729378197 == 3)) && (input.equals("H"))) && (a123124249.equals("h")))) {
    	cf = false;
    	a123124249 = "e";
    	a145848903 = "h"; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm17(String input) {
    if((cf && (a198422080 == 6))) {
    	calculateOutputm136(input);
    } 
    if(((a198422080 == 7) && cf)) {
    	calculateOutputm137(input);
    } 
    if(((a198422080 == 11) && cf)) {
    	calculateOutputm140(input);
    } 
}
private  void calculateOutputm141(String input) {
    if(((a366362113.equals("e")) && ((a1729378197 == 3) && (((a123124249.equals("i")) && cf) && (input.equals("A")))))) {
    	cf = false;
    	a1729378197 = 2;
    	a1477849038 = "g";
    	a541989745 = 7; 
    	System.out.println("P");
    } if(((a123124249.equals("i")) && ((a366362113.equals("e")) && ((a1729378197 == 3) && ((input.equals("H")) && cf))))) {
    	cf = false;
    	a1729378197 = 5;
    	a23351479 = 9; 
    	System.out.println("V");
    } if((((((a1729378197 == 3) && cf) && (a123124249.equals("i"))) && (a366362113.equals("e"))) && (input.equals("D")))) {
    	cf = false;
    	a1477849038 = "g";
    	a1584317767 = "e";
    	a1729378197 = 4; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm142(String input) {
    if(((((cf && (input.equals("C"))) && (a123124249.equals("i"))) && (a366362113.equals("h"))) && (a1729378197 == 3))) {
    	cf = false;
    	a1937499914 = "i";
    	a1729378197 = 1;
    	a938681481 = 13; 
    	System.out.println("Z");
    } if((((input.equals("J")) && ((a123124249.equals("i")) && ((a1729378197 == 3) && cf))) && (a366362113.equals("h")))) {
    	cf = false;
    	 
    	System.out.println("S");
    } if(((input.equals("K")) && ((a366362113.equals("h")) && (((a1729378197 == 3) && cf) && (a123124249.equals("i")))))) {
    	cf = false;
    	a938681481 = 7;
    	a1729378197 = 1;
    	a1716763601 = 5; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm143(String input) {
    if(((input.equals("K")) && ((a366362113.equals("i")) && ((a123124249.equals("i")) && (cf && (a1729378197 == 3)))))) {
    	cf = false;
    	a1245641101 = "i";
    	a1729378197 = 7;
    	a1920565083 = 10; 
    	System.out.println("Q");
    } if((((input.equals("L")) && (((a366362113.equals("i")) && cf) && (a1729378197 == 3))) && (a123124249.equals("i")))) {
    	cf = false;
    	a1729378197 = 1;
    	a1937499914 = "f";
    	a938681481 = 13; 
    	System.out.println("Q");
    } if(((((a1729378197 == 3) && ((input.equals("M")) && cf)) && (a366362113.equals("i"))) && (a123124249.equals("i")))) {
    	cf = false;
    	a1937499914 = "f";
    	a1729378197 = 1;
    	a938681481 = 13; 
    	System.out.println("Q");
    } if(((input.equals("O")) && ((a1729378197 == 3) && (((a366362113.equals("i")) && cf) && (a123124249.equals("i")))))) {
    	cf = false;
    	 
    	System.out.println("X");
    } 
}
private  void calculateOutputm18(String input) {
    if((cf && (a366362113.equals("e")))) {
    	calculateOutputm141(input);
    } 
    if(((a366362113.equals("h")) && cf)) {
    	calculateOutputm142(input);
    } 
    if(((a366362113.equals("i")) && cf)) {
    	calculateOutputm143(input);
    } 
}
private  void calculateOutputm144(String input) {
    if((((a1729378197 == 4) && ((cf && (input.equals("D"))) && (a1477849038.equals("e")))) && (a1716858626.equals("e")))) {
    	cf = false;
    	a1729378197 = 1;
    	a1937499914 = "f";
    	a938681481 = 13; 
    	System.out.println("Q");
    } if(((a1477849038.equals("e")) && ((a1716858626.equals("e")) && ((input.equals("G")) && (cf && (a1729378197 == 4)))))) {
    	cf = false;
    	a1729378197 = 8;
    	a847841994 = "f";
    	a299375216 = 1; 
    	System.out.println("S");
    } if((((a1477849038.equals("e")) && ((a1716858626.equals("e")) && (cf && (a1729378197 == 4)))) && (input.equals("H")))) {
    	cf = false;
    	a847841994 = "f";
    	a1729378197 = 8;
    	a299375216 = 1; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm145(String input) {
    if(((a1716858626.equals("f")) && ((input.equals("F")) && ((cf && (a1729378197 == 4)) && (a1477849038.equals("e")))))) {
    	cf = false;
    	a23351479 = 10;
    	a1729378197 = 5;
    	a37252965 = 11; 
    	System.out.println("Q");
    } if((((a1729378197 == 4) && (((a1716858626.equals("f")) && cf) && (a1477849038.equals("e")))) && (input.equals("L")))) {
    	cf = false;
    	a1729378197 = 8;
    	a1039409491 = "e";
    	a299375216 = 6; 
    	System.out.println("X");
    } 
}
private  void calculateOutputm19(String input) {
    if((cf && (a1716858626.equals("e")))) {
    	calculateOutputm144(input);
    } 
    if(((a1716858626.equals("f")) && cf)) {
    	calculateOutputm145(input);
    } 
}
private  void calculateOutputm147(String input) {
    if(((a1477849038.equals("f")) && ((input.equals("B")) && ((a1729378197 == 4) && ((a1570444282.equals("f")) && cf))))) {
    	cf = false;
    	a1584317767 = "h";
    	a123124249 = "f";
    	a1729378197 = 3; 
    	System.out.println("W");
    } if(((a1729378197 == 4) && ((((input.equals("H")) && cf) && (a1477849038.equals("f"))) && (a1570444282.equals("f"))))) {
    	cf = false;
    	a23351479 = 10;
    	a1729378197 = 5;
    	a37252965 = 9; 
    	System.out.println("S");
    } if(((a1477849038.equals("f")) && ((((a1729378197 == 4) && cf) && (a1570444282.equals("f"))) && (input.equals("M"))))) {
    	cf = false;
    	a938681481 = 11;
    	a1729378197 = 1;
    	a1892947393 = 8; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm148(String input) {
    if((((a1570444282.equals("g")) && (((input.equals("F")) && cf) && (a1477849038.equals("f")))) && (a1729378197 == 4))) {
    	cf = false;
    	a1306585414 = "g";
    	a1729378197 = 8;
    	a299375216 = 7; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm20(String input) {
    if(((a1570444282.equals("f")) && cf)) {
    	calculateOutputm147(input);
    } 
    if((cf && (a1570444282.equals("g")))) {
    	calculateOutputm148(input);
    } 
}
private  void calculateOutputm152(String input) {
    if(((input.equals("L")) && ((a1584317767.equals("f")) && (((a1729378197 == 4) && cf) && (a1477849038.equals("g")))))) {
    	cf = false;
    	a1729378197 = 6;
    	a1047798024 = "g";
    	a23351479 = 14; 
    	System.out.println("P");
    } if((((a1729378197 == 4) && ((a1584317767.equals("f")) && ((a1477849038.equals("g")) && cf))) && (input.equals("O")))) {
    	cf = false;
    	a1729378197 = 7;
    	a650861711 = "f";
    	a1920565083 = 9; 
    	System.out.println("W");
    } 
}
private  void calculateOutputm153(String input) {
    if(((input.equals("F")) && ((a1477849038.equals("g")) && ((a1584317767.equals("g")) && ((a1729378197 == 4) && cf))))) {
    	cf = false;
    	a674877 = "i";
    	a1477849038 = "e";
    	a1729378197 = 2; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm155(String input) {
    if(((input.equals("A")) && ((a1729378197 == 4) && ((a1477849038.equals("g")) && (cf && (a1584317767.equals("i"))))))) {
    	cf = false;
    	a847841994 = "f";
    	a1729378197 = 8;
    	a299375216 = 1; 
    	System.out.println("S");
    } if((((a1729378197 == 4) && (((a1477849038.equals("g")) && cf) && (a1584317767.equals("i")))) && (input.equals("B")))) {
    	cf = false;
    	 
    	System.out.println("S");
    } 
}
private  void calculateOutputm21(String input) {
    if((cf && (a1584317767.equals("f")))) {
    	calculateOutputm152(input);
    } 
    if(((a1584317767.equals("g")) && cf)) {
    	calculateOutputm153(input);
    } 
    if(((a1584317767.equals("i")) && cf)) {
    	calculateOutputm155(input);
    } 
}
private  void calculateOutputm156(String input) {
    if(((a1729378197 == 4) && ((input.equals("B")) && ((cf && (a1477849038.equals("h"))) && (a1114110175.equals("e")))))) {
    	cf = false;
    	a1729378197 = 7;
    	a68550605 = "f";
    	a1920565083 = 14; 
    	System.out.println("S");
    } if(((a1477849038.equals("h")) && ((input.equals("G")) && ((a1729378197 == 4) && ((a1114110175.equals("e")) && cf))))) {
    	cf = false;
    	a1729378197 = 7;
    	a1245641101 = "f";
    	a1920565083 = 10; 
    	System.out.println("Q");
    } if(((a1477849038.equals("h")) && ((a1729378197 == 4) && ((input.equals("K")) && ((a1114110175.equals("e")) && cf))))) {
    	cf = false;
    	a1039409491 = "g";
    	a1729378197 = 8;
    	a299375216 = 6; 
    	System.out.println("R");
    } if(((a1114110175.equals("e")) && ((a1729378197 == 4) && ((a1477849038.equals("h")) && ((input.equals("O")) && cf))))) {
    	cf = false;
    	a650861711 = "f";
    	a1729378197 = 7;
    	a1920565083 = 9; 
    	System.out.println("X");
    } 
}
private  void calculateOutputm158(String input) {
    if(((a1729378197 == 4) && ((((input.equals("F")) && cf) && (a1477849038.equals("h"))) && (a1114110175.equals("i"))))) {
    	cf = false;
    	a1729378197 = 2;
    	a1477849038 = "g";
    	a541989745 = 5; 
    	System.out.println("X");
    } if(((a1114110175.equals("i")) && ((a1477849038.equals("h")) && ((input.equals("G")) && ((a1729378197 == 4) && cf))))) {
    	cf = false;
    	a1729378197 = 1;
    	a1937499914 = "f";
    	a938681481 = 13; 
    	System.out.println("Q");
    } if(((((input.equals("L")) && ((a1114110175.equals("i")) && cf)) && (a1729378197 == 4)) && (a1477849038.equals("h")))) {
    	cf = false;
    	a23351479 = 10;
    	a1729378197 = 5;
    	a37252965 = 11; 
    	System.out.println("S");
    } if(((a1477849038.equals("h")) && (((input.equals("O")) && ((a1729378197 == 4) && cf)) && (a1114110175.equals("i"))))) {
    	cf = false;
    	a1047798024 = "g";
    	a1729378197 = 6;
    	a23351479 = 12; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm22(String input) {
    if(((a1114110175.equals("e")) && cf)) {
    	calculateOutputm156(input);
    } 
    if((cf && (a1114110175.equals("i")))) {
    	calculateOutputm158(input);
    } 
}
private  void calculateOutputm160(String input) {
    if(((a50296898 == 10) && ((a1729378197 == 4) && ((a1477849038.equals("i")) && ((input.equals("C")) && cf))))) {
    	cf = false;
    	a123124249 = "e";
    	a145848903 = "h";
    	a1729378197 = 3; 
    	System.out.println("S");
    } if(((input.equals("H")) && ((a50296898 == 10) && (((a1477849038.equals("i")) && cf) && (a1729378197 == 4))))) {
    	cf = false;
    	a123124249 = "i";
    	a366362113 = "i";
    	a1729378197 = 3; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm161(String input) {
    if(((a50296898 == 11) && ((a1729378197 == 4) && ((a1477849038.equals("i")) && (cf && (input.equals("B"))))))) {
    	cf = false;
    	a1729378197 = 7;
    	a1920565083 = 13;
    	a1518235786 = 5; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm23(String input) {
    if((cf && (a50296898 == 10))) {
    	calculateOutputm160(input);
    } 
    if((cf && (a50296898 == 11))) {
    	calculateOutputm161(input);
    } 
}
private  void calculateOutputm164(String input) {
    if((((input.equals("A")) && (((a23351479 == 9) && cf) && (a123124249.equals("e")))) && (a1729378197 == 5))) {
    	cf = false;
    	a366362113 = "h";
    	a123124249 = "i";
    	a1729378197 = 3; 
    	System.out.println("S");
    } if((((a123124249.equals("e")) && (((input.equals("G")) && cf) && (a1729378197 == 5))) && (a23351479 == 9))) {
    	cf = false;
    	a674877 = "e";
    	a1477849038 = "e";
    	a1729378197 = 2; 
    	System.out.println("X");
    } 
}
private  void calculateOutputm165(String input) {
    if(((((cf && (a23351479 == 9)) && (input.equals("A"))) && (a123124249.equals("f"))) && (a1729378197 == 5))) {
    	cf = false;
    	a123124249 = "e";
    	a145848903 = "h";
    	a1729378197 = 3; 
    	System.out.println("T");
    } if((((a23351479 == 9) && ((input.equals("D")) && (cf && (a1729378197 == 5)))) && (a123124249.equals("f")))) {
    	cf = false;
    	a1729378197 = 7;
    	a1920565083 = 8;
    	a1668586383 = 7; 
    	System.out.println("U");
    } if(((a1729378197 == 5) && (((input.equals("H")) && (cf && (a23351479 == 9))) && (a123124249.equals("f"))))) {
    	cf = false;
    	a1729378197 = 7;
    	a68550605 = "i";
    	a1920565083 = 14; 
    	System.out.println("Q");
    } if(((a23351479 == 9) && ((a123124249.equals("f")) && (((a1729378197 == 5) && cf) && (input.equals("J")))))) {
    	cf = false;
    	a123124249 = "i";
    	a366362113 = "i";
    	a1729378197 = 3; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm166(String input) {
    if((((a23351479 == 9) && ((a123124249.equals("g")) && (cf && (a1729378197 == 5)))) && (input.equals("G")))) {
    	cf = false;
    	a23351479 = 14;
    	a871304185 = 5; 
    	System.out.println("Y");
    } if(((a23351479 == 9) && ((a1729378197 == 5) && ((input.equals("K")) && (cf && (a123124249.equals("g"))))))) {
    	cf = false;
    	a1047798024 = "f";
    	a24442901 = "e";
    	a1729378197 = 6; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm168(String input) {
    if(((input.equals("C")) && ((a1729378197 == 5) && ((a23351479 == 9) && (cf && (a123124249.equals("i"))))))) {
    	cf = false;
    	a1047798024 = "h";
    	a1729378197 = 8;
    	a299375216 = 2; 
    	System.out.println("U");
    } if(((((a1729378197 == 5) && (cf && (a23351479 == 9))) && (a123124249.equals("i"))) && (input.equals("J")))) {
    	cf = false;
    	a650861711 = "i";
    	a1729378197 = 7;
    	a1920565083 = 9; 
    	System.out.println("V");
    } if(((input.equals("M")) && (((cf && (a1729378197 == 5)) && (a123124249.equals("i"))) && (a23351479 == 9)))) {
    	cf = false;
    	a847841994 = "h";
    	a1729378197 = 8;
    	a299375216 = 1; 
    	System.out.println("T");
    } if(((a1729378197 == 5) && ((a123124249.equals("i")) && ((a23351479 == 9) && (cf && (input.equals("O"))))))) {
    	cf = false;
    	a1583272058 = "h";
    	a1047798024 = "e";
    	a1729378197 = 6; 
    	System.out.println("V");
    } if(((a1729378197 == 5) && (((a123124249.equals("i")) && ((input.equals("E")) && cf)) && (a23351479 == 9)))) {
    	cf = false;
    	a938681481 = 11;
    	a1729378197 = 1;
    	a1892947393 = 11; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm24(String input) {
    if((cf && (a123124249.equals("e")))) {
    	calculateOutputm164(input);
    } 
    if((cf && (a123124249.equals("f")))) {
    	calculateOutputm165(input);
    } 
    if((cf && (a123124249.equals("g")))) {
    	calculateOutputm166(input);
    } 
    if(((a123124249.equals("i")) && cf)) {
    	calculateOutputm168(input);
    } 
}
private  void calculateOutputm169(String input) {
    if(((((a1729378197 == 5) && ((a23351479 == 10) && cf)) && (a37252965 == 8)) && (input.equals("G")))) {
    	cf = false;
    	a1039409491 = "f";
    	a1729378197 = 8;
    	a299375216 = 6; 
    	System.out.println("Q");
    } if(((a1729378197 == 5) && (((cf && (a23351479 == 10)) && (input.equals("M"))) && (a37252965 == 8)))) {
    	cf = false;
    	a1729378197 = 7;
    	a1920565083 = 15;
    	a1105418891 = 12; 
    	System.out.println("R");
    } 
}
private  void calculateOutputm170(String input) {
    if(((a1729378197 == 5) && ((a23351479 == 10) && ((cf && (input.equals("K"))) && (a37252965 == 9))))) {
    	cf = false;
    	 
    	System.out.println("W");
    } if(((((a37252965 == 9) && (cf && (input.equals("M")))) && (a23351479 == 10)) && (a1729378197 == 5))) {
    	cf = false;
    	a37252965 = 15; 
    	System.out.println("X");
    } if(((input.equals("O")) && ((a37252965 == 9) && (((a1729378197 == 5) && cf) && (a23351479 == 10))))) {
    	cf = false;
    	 
    	System.out.println("W");
    } 
}
private  void calculateOutputm171(String input) {
    if((((((a1729378197 == 5) && cf) && (input.equals("G"))) && (a37252965 == 10)) && (a23351479 == 10))) {
    	cf = false;
    	a37252965 = 11; 
    	System.out.println("P");
    } if(((a23351479 == 10) && ((a37252965 == 10) && ((cf && (input.equals("H"))) && (a1729378197 == 5))))) {
    	cf = false;
    	a674877 = "f";
    	a1477849038 = "e";
    	a1729378197 = 2; 
    	System.out.println("Z");
    } if((((a23351479 == 10) && (((input.equals("M")) && cf) && (a1729378197 == 5))) && (a37252965 == 10))) {
    	cf = false;
    	a1245641101 = "f";
    	a1729378197 = 7;
    	a1920565083 = 10; 
    	System.out.println("R");
    } 
}
private  void calculateOutputm172(String input) {
    if(((((cf && (a23351479 == 10)) && (input.equals("H"))) && (a1729378197 == 5)) && (a37252965 == 11))) {
    	cf = false;
    	a1047798024 = "g";
    	a1729378197 = 6; 
    	System.out.println("V");
    } if((((a37252965 == 11) && ((cf && (a1729378197 == 5)) && (input.equals("J")))) && (a23351479 == 10))) {
    	cf = false;
    	a1729378197 = 1;
    	a911974320 = "h";
    	a938681481 = 9; 
    	System.out.println("X");
    } if(((input.equals("E")) && ((((a37252965 == 11) && cf) && (a23351479 == 10)) && (a1729378197 == 5)))) {
    	cf = false;
    	a145848903 = "f";
    	a123124249 = "e";
    	a1729378197 = 3; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm173(String input) {
    if((((a37252965 == 12) && ((cf && (a1729378197 == 5)) && (a23351479 == 10))) && (input.equals("F")))) {
    	cf = false;
    	a1477849038 = "h";
    	a1114110175 = "i";
    	a1729378197 = 4; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm174(String input) {
    if((((a23351479 == 10) && ((cf && (input.equals("G"))) && (a1729378197 == 5))) && (a37252965 == 13))) {
    	cf = false;
    	a1047798024 = "f";
    	a24442901 = "h";
    	a1729378197 = 6; 
    	System.out.println("W");
    } if((((input.equals("M")) && ((a23351479 == 10) && (cf && (a37252965 == 13)))) && (a1729378197 == 5))) {
    	cf = false;
    	a24442901 = "f";
    	a1047798024 = "f";
    	a1729378197 = 6; 
    	System.out.println("T");
    } if((((input.equals("I")) && (((a1729378197 == 5) && cf) && (a37252965 == 13))) && (a23351479 == 10))) {
    	cf = false;
    	a853421711 = "i";
    	a1729378197 = 8;
    	a299375216 = 8; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm175(String input) {
    if(((a23351479 == 10) && ((input.equals("C")) && ((cf && (a37252965 == 14)) && (a1729378197 == 5))))) {
    	cf = false;
    	a1477849038 = "g";
    	a1584317767 = "i";
    	a1729378197 = 4; 
    	System.out.println("U");
    } if((((a23351479 == 10) && (((input.equals("J")) && cf) && (a1729378197 == 5))) && (a37252965 == 14))) {
    	cf = false;
    	a938681481 = 10;
    	a1729378197 = 1;
    	a198422080 = 10; 
    	System.out.println("X");
    } if(((input.equals("O")) && ((a23351479 == 10) && ((a37252965 == 14) && ((a1729378197 == 5) && cf))))) {
    	cf = false;
    	a1477849038 = "h";
    	a1114110175 = "i";
    	a1729378197 = 4; 
    	System.out.println("P");
    } 
}
private  void calculateOutputm176(String input) {
    if(((a37252965 == 15) && ((input.equals("A")) && ((a23351479 == 10) && (cf && (a1729378197 == 5)))))) {
    	cf = false;
    	a938681481 = 12;
    	a1729378197 = 1;
    	a1075056448 = 7; 
    	System.out.println("Q");
    } if(((a37252965 == 15) && ((a23351479 == 10) && ((cf && (a1729378197 == 5)) && (input.equals("H")))))) {
    	cf = false;
    	a938681481 = 10;
    	a1729378197 = 1;
    	a198422080 = 12; 
    	System.out.println("Z");
    } if(((input.equals("L")) && ((a23351479 == 10) && ((a37252965 == 15) && (cf && (a1729378197 == 5)))))) {
    	cf = false;
    	a37252965 = 9; 
    	System.out.println("W");
    } if(((((a23351479 == 10) && ((a1729378197 == 5) && cf)) && (input.equals("O"))) && (a37252965 == 15))) {
    	cf = false;
    	a1039409491 = "g";
    	a1729378197 = 8;
    	a299375216 = 6; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm25(String input) {
    if((cf && (a37252965 == 8))) {
    	calculateOutputm169(input);
    } 
    if(((a37252965 == 9) && cf)) {
    	calculateOutputm170(input);
    } 
    if(((a37252965 == 10) && cf)) {
    	calculateOutputm171(input);
    } 
    if((cf && (a37252965 == 11))) {
    	calculateOutputm172(input);
    } 
    if(((a37252965 == 12) && cf)) {
    	calculateOutputm173(input);
    } 
    if((cf && (a37252965 == 13))) {
    	calculateOutputm174(input);
    } 
    if((cf && (a37252965 == 14))) {
    	calculateOutputm175(input);
    } 
    if((cf && (a37252965 == 15))) {
    	calculateOutputm176(input);
    } 
}
private  void calculateOutputm178(String input) {
    if((((a1729378197 == 5) && ((a520438996 == 5) && ((a23351479 == 11) && cf))) && (input.equals("F")))) {
    	cf = false;
    	a1729378197 = 8;
    	a1039409491 = "e";
    	a299375216 = 6; 
    	System.out.println("S");
    } if((((input.equals("H")) && ((cf && (a1729378197 == 5)) && (a23351479 == 11))) && (a520438996 == 5))) {
    	cf = false;
    	a1584317767 = "h";
    	a123124249 = "f";
    	a1729378197 = 3; 
    	System.out.println("S");
    } if((((a1729378197 == 5) && (((input.equals("O")) && cf) && (a520438996 == 5))) && (a23351479 == 11))) {
    	cf = false;
    	a1584317767 = "i";
    	a1477849038 = "g";
    	a1729378197 = 4; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm181(String input) {
    if(((a23351479 == 11) && ((((a1729378197 == 5) && cf) && (input.equals("D"))) && (a520438996 == 8)))) {
    	cf = false;
    	a366362113 = "i";
    	a123124249 = "i";
    	a1729378197 = 3; 
    	System.out.println("Q");
    } if(((a520438996 == 8) && ((input.equals("H")) && (((a23351479 == 11) && cf) && (a1729378197 == 5))))) {
    	cf = false;
    	a1729378197 = 8;
    	a1039409491 = "g";
    	a299375216 = 6; 
    	System.out.println("S");
    } if(((a520438996 == 8) && ((a1729378197 == 5) && (((a23351479 == 11) && cf) && (input.equals("J")))))) {
    	cf = false;
    	a145848903 = "h";
    	a123124249 = "e";
    	a1729378197 = 3; 
    	System.out.println("V");
    } if((((a1729378197 == 5) && (((a520438996 == 8) && cf) && (input.equals("K")))) && (a23351479 == 11))) {
    	cf = false;
    	a1477849038 = "e";
    	a674877 = "e";
    	a1729378197 = 2; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm183(String input) {
    if(((((input.equals("D")) && ((a520438996 == 10) && cf)) && (a1729378197 == 5)) && (a23351479 == 11))) {
    	cf = false;
    	a839019366 = "i";
    	a23351479 = 13; 
    	System.out.println("W");
    } if(((((a23351479 == 11) && ((a520438996 == 10) && cf)) && (a1729378197 == 5)) && (input.equals("G")))) {
    	cf = false;
    	a1729378197 = 7;
    	a1245641101 = "e";
    	a1920565083 = 10; 
    	System.out.println("S");
    } if(((a520438996 == 10) && (((cf && (a1729378197 == 5)) && (a23351479 == 11)) && (input.equals("K"))))) {
    	cf = false;
    	a23351479 = 10;
    	a37252965 = 14; 
    	System.out.println("W");
    } 
}
private  void calculateOutputm184(String input) {
    if((((((input.equals("C")) && cf) && (a23351479 == 11)) && (a1729378197 == 5)) && (a520438996 == 11))) {
    	cf = false;
    	a1477849038 = "h";
    	a1114110175 = "i";
    	a1729378197 = 4; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm26(String input) {
    if(((a520438996 == 5) && cf)) {
    	calculateOutputm178(input);
    } 
    if((cf && (a520438996 == 8))) {
    	calculateOutputm181(input);
    } 
    if(((a520438996 == 10) && cf)) {
    	calculateOutputm183(input);
    } 
    if(((a520438996 == 11) && cf)) {
    	calculateOutputm184(input);
    } 
}
private  void calculateOutputm187(String input) {
    if(((a1729378197 == 5) && (((input.equals("O")) && ((a1803458941 == 15) && cf)) && (a23351479 == 12)))) {
    	cf = false;
    	a1729378197 = 8;
    	a847841994 = "i";
    	a299375216 = 1; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm189(String input) {
    if(((a1803458941 == 17) && ((a23351479 == 12) && ((input.equals("C")) && ((a1729378197 == 5) && cf))))) {
    	cf = false;
    	a674877 = "e";
    	a1477849038 = "e";
    	a1729378197 = 2; 
    	System.out.println("S");
    } if(((a23351479 == 12) && ((a1803458941 == 17) && (((a1729378197 == 5) && cf) && (input.equals("F")))))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 12;
    	a1075056448 = 7; 
    	System.out.println("S");
    } if(((a1803458941 == 17) && ((input.equals("G")) && ((a23351479 == 12) && ((a1729378197 == 5) && cf))))) {
    	cf = false;
    	a1729378197 = 2;
    	a1477849038 = "g";
    	a541989745 = 8; 
    	System.out.println("S");
    } if((((a1803458941 == 17) && (((a1729378197 == 5) && cf) && (a23351479 == 12))) && (input.equals("O")))) {
    	cf = false;
    	a1729378197 = 6;
    	a1047798024 = "g";
    	a23351479 = 13; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm27(String input) {
    if((cf && (a1803458941 == 15))) {
    	calculateOutputm187(input);
    } 
    if((cf && (a1803458941 == 17))) {
    	calculateOutputm189(input);
    } 
}
private  void calculateOutputm191(String input) {
    if((((((a1729378197 == 5) && cf) && (a23351479 == 13)) && (input.equals("A"))) && (a839019366.equals("f")))) {
    	cf = false;
    	a1105727296 = "h";
    	a1729378197 = 8;
    	a299375216 = 5; 
    	System.out.println("U");
    } if(((((a839019366.equals("f")) && ((a1729378197 == 5) && cf)) && (a23351479 == 13)) && (input.equals("C")))) {
    	cf = false;
    	a1477849038 = "f";
    	a625366011 = "h";
    	a1729378197 = 2; 
    	System.out.println("Q");
    } if(((a23351479 == 13) && (((cf && (input.equals("D"))) && (a1729378197 == 5)) && (a839019366.equals("f"))))) {
    	cf = false;
    	a938681481 = 11;
    	a1729378197 = 1;
    	a1892947393 = 6; 
    	System.out.println("Q");
    } if((((a23351479 == 13) && ((cf && (input.equals("J"))) && (a1729378197 == 5))) && (a839019366.equals("f")))) {
    	cf = false;
    	a24442901 = "g";
    	a1047798024 = "f";
    	a1729378197 = 6; 
    	System.out.println("V");
    } 
}
private  void calculateOutputm193(String input) {
    if((((a23351479 == 13) && ((a839019366.equals("h")) && ((input.equals("L")) && cf))) && (a1729378197 == 5))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 12;
    	a1075056448 = 7; 
    	System.out.println("X");
    } 
}
private  void calculateOutputm194(String input) {
    if((((a839019366.equals("i")) && ((a23351479 == 13) && (cf && (input.equals("D"))))) && (a1729378197 == 5))) {
    	cf = false;
    	a1729378197 = 8;
    	a1039409491 = "g";
    	a299375216 = 6; 
    	System.out.println("R");
    } if((((input.equals("K")) && ((a23351479 == 13) && ((a1729378197 == 5) && cf))) && (a839019366.equals("i")))) {
    	cf = false;
    	a674877 = "e";
    	a1477849038 = "e";
    	a1729378197 = 2; 
    	System.out.println("S");
    } if(((a1729378197 == 5) && ((((a23351479 == 13) && cf) && (input.equals("M"))) && (a839019366.equals("i"))))) {
    	cf = false;
    	a1477849038 = "h";
    	a1114110175 = "i";
    	a1729378197 = 4; 
    	System.out.println("T");
    } if(((a839019366.equals("i")) && (((cf && (a1729378197 == 5)) && (input.equals("O"))) && (a23351479 == 13)))) {
    	cf = false;
    	a938681481 = 10;
    	a1729378197 = 1;
    	a198422080 = 10; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm28(String input) {
    if((cf && (a839019366.equals("f")))) {
    	calculateOutputm191(input);
    } 
    if(((a839019366.equals("h")) && cf)) {
    	calculateOutputm193(input);
    } 
    if(((a839019366.equals("i")) && cf)) {
    	calculateOutputm194(input);
    } 
}
private  void calculateOutputm195(String input) {
    if(((((cf && (a871304185 == 3)) && (a1729378197 == 5)) && (input.equals("F"))) && (a23351479 == 14))) {
    	cf = false;
    	a299375216 = 3;
    	a1729378197 = 8;
    	a310220227 = 9; 
    	System.out.println("Q");
    } if((((input.equals("O")) && ((a871304185 == 3) && ((a23351479 == 14) && cf))) && (a1729378197 == 5))) {
    	cf = false;
    	a1729378197 = 7;
    	a68550605 = "i";
    	a1920565083 = 14; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm196(String input) {
    if((((a871304185 == 4) && (((a1729378197 == 5) && cf) && (a23351479 == 14))) && (input.equals("L")))) {
    	cf = false;
    	a23351479 = 15;
    	a948298434 = 12; 
    	System.out.println("Z");
    } if(((a1729378197 == 5) && (((a871304185 == 4) && (cf && (a23351479 == 14))) && (input.equals("O"))))) {
    	cf = false;
    	a1920565083 = 11;
    	a1729378197 = 7;
    	a312388145 = 10; 
    	System.out.println("W");
    } if(((input.equals("B")) && (((a1729378197 == 5) && ((a871304185 == 4) && cf)) && (a23351479 == 14)))) {
    	cf = false;
    	a1729378197 = 7;
    	a68550605 = "g";
    	a1920565083 = 14; 
    	System.out.println("X");
    } 
}
private  void calculateOutputm197(String input) {
    if((((a23351479 == 14) && (((a1729378197 == 5) && cf) && (a871304185 == 5))) && (input.equals("A")))) {
    	cf = false;
    	a1729378197 = 3;
    	a123124249 = "g";
    	a1091978491 = 11; 
    	System.out.println("X");
    } 
}
private  void calculateOutputm198(String input) {
    if(((a1729378197 == 5) && ((a871304185 == 6) && ((cf && (input.equals("O"))) && (a23351479 == 14))))) {
    	cf = false;
    	a1729378197 = 2;
    	a1477849038 = "g";
    	a541989745 = 8; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm199(String input) {
    if(((((a23351479 == 14) && ((input.equals("F")) && cf)) && (a1729378197 == 5)) && (a871304185 == 7))) {
    	cf = false;
    	a871304185 = 8; 
    	System.out.println("X");
    } if(((a871304185 == 7) && ((input.equals("K")) && ((a1729378197 == 5) && (cf && (a23351479 == 14)))))) {
    	cf = false;
    	a123124249 = "e";
    	a145848903 = "h";
    	a1729378197 = 3; 
    	System.out.println("R");
    } if(((a23351479 == 14) && (((cf && (a871304185 == 7)) && (a1729378197 == 5)) && (input.equals("M"))))) {
    	cf = false;
    	a1729378197 = 8;
    	a299375216 = 3;
    	a310220227 = 7; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm200(String input) {
    if(((a23351479 == 14) && (((input.equals("G")) && (cf && (a1729378197 == 5))) && (a871304185 == 8)))) {
    	cf = false;
    	a1729378197 = 1;
    	a1937499914 = "f";
    	a938681481 = 13; 
    	System.out.println("Q");
    } if((((input.equals("M")) && (((a871304185 == 8) && cf) && (a23351479 == 14))) && (a1729378197 == 5))) {
    	cf = false;
    	a1937499914 = "f";
    	a1729378197 = 1;
    	a938681481 = 13; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm29(String input) {
    if((cf && (a871304185 == 3))) {
    	calculateOutputm195(input);
    } 
    if(((a871304185 == 4) && cf)) {
    	calculateOutputm196(input);
    } 
    if((cf && (a871304185 == 5))) {
    	calculateOutputm197(input);
    } 
    if(((a871304185 == 6) && cf)) {
    	calculateOutputm198(input);
    } 
    if((cf && (a871304185 == 7))) {
    	calculateOutputm199(input);
    } 
    if(((a871304185 == 8) && cf)) {
    	calculateOutputm200(input);
    } 
}
private  void calculateOutputm202(String input) {
    if(((((cf && (a1729378197 == 5)) && (input.equals("A"))) && (a23351479 == 15)) && (a948298434 == 7))) {
    	cf = false;
    	a1729378197 = 8;
    	a299375216 = 3;
    	a310220227 = 10; 
    	System.out.println("P");
    } if(((a1729378197 == 5) && (((a948298434 == 7) && ((input.equals("H")) && cf)) && (a23351479 == 15)))) {
    	cf = false;
    	 
    	System.out.println("U");
    } if(((a1729378197 == 5) && (((a948298434 == 7) && ((input.equals("L")) && cf)) && (a23351479 == 15)))) {
    	cf = false;
    	a1114110175 = "i";
    	a1477849038 = "h";
    	a1729378197 = 4; 
    	System.out.println("Z");
    } if(((((cf && (a948298434 == 7)) && (input.equals("O"))) && (a1729378197 == 5)) && (a23351479 == 15))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 7;
    	a1716763601 = 5; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm204(String input) {
    if(((((input.equals("B")) && (cf && (a948298434 == 9))) && (a23351479 == 15)) && (a1729378197 == 5))) {
    	cf = false;
    	a847841994 = "i";
    	a1729378197 = 8;
    	a299375216 = 1; 
    	System.out.println("T");
    } if(((a1729378197 == 5) && ((input.equals("C")) && ((a23351479 == 15) && (cf && (a948298434 == 9)))))) {
    	cf = false;
    	a1729378197 = 3;
    	a123124249 = "g";
    	a1091978491 = 11; 
    	System.out.println("T");
    } if(((((input.equals("F")) && (cf && (a948298434 == 9))) && (a23351479 == 15)) && (a1729378197 == 5))) {
    	cf = false;
    	a1039409491 = "e";
    	a1729378197 = 8;
    	a299375216 = 6; 
    	System.out.println("X");
    } if(((((a948298434 == 9) && (cf && (input.equals("J")))) && (a1729378197 == 5)) && (a23351479 == 15))) {
    	cf = false;
    	a1047798024 = "i";
    	a911974320 = "g";
    	a1729378197 = 6; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm206(String input) {
    if(((a948298434 == 12) && ((a23351479 == 15) && ((a1729378197 == 5) && (cf && (input.equals("K"))))))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 10;
    	a198422080 = 10; 
    	System.out.println("P");
    } if(((a1729378197 == 5) && (((cf && (a23351479 == 15)) && (input.equals("O"))) && (a948298434 == 12)))) {
    	cf = false;
    	a1729378197 = 2;
    	a1477849038 = "g";
    	a541989745 = 8; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm207(String input) {
    if(((input.equals("D")) && ((a1729378197 == 5) && (((a23351479 == 15) && cf) && (a948298434 == 13))))) {
    	cf = false;
    	a1729378197 = 6;
    	a1047798024 = "g";
    	a23351479 = 14; 
    	System.out.println("Z");
    } if(((a1729378197 == 5) && ((input.equals("G")) && ((cf && (a23351479 == 15)) && (a948298434 == 13))))) {
    	cf = false;
    	a299375216 = 4;
    	a1729378197 = 8;
    	a1105418891 = 11; 
    	System.out.println("W");
    } 
}
private  void calculateOutputm30(String input) {
    if(((a948298434 == 7) && cf)) {
    	calculateOutputm202(input);
    } 
    if(((a948298434 == 9) && cf)) {
    	calculateOutputm204(input);
    } 
    if(((a948298434 == 12) && cf)) {
    	calculateOutputm206(input);
    } 
    if((cf && (a948298434 == 13))) {
    	calculateOutputm207(input);
    } 
}
private  void calculateOutputm209(String input) {
    if(((a23351479 == 16) && ((a583157892.equals("f")) && ((a1729378197 == 5) && ((input.equals("J")) && cf))))) {
    	cf = false;
    	a1729378197 = 7;
    	a1920565083 = 13;
    	a1518235786 = 10; 
    	System.out.println("S");
    } if(((a1729378197 == 5) && ((a583157892.equals("f")) && (((a23351479 == 16) && cf) && (input.equals("K")))))) {
    	cf = false;
    	a23351479 = 14;
    	a871304185 = 8; 
    	System.out.println("S");
    } if((((a583157892.equals("f")) && ((input.equals("M")) && (cf && (a1729378197 == 5)))) && (a23351479 == 16))) {
    	cf = false;
    	a1729378197 = 7;
    	a68550605 = "f";
    	a1920565083 = 14; 
    	System.out.println("S");
    } if((((a583157892.equals("f")) && (((a1729378197 == 5) && cf) && (input.equals("O")))) && (a23351479 == 16))) {
    	cf = false;
    	a1584317767 = "i";
    	a1477849038 = "g";
    	a1729378197 = 4; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm31(String input) {
    if((cf && (a583157892.equals("f")))) {
    	calculateOutputm209(input);
    } 
}
private  void calculateOutputm214(String input) {
    if((((input.equals("J")) && ((cf && (a1047798024.equals("e"))) && (a1583272058.equals("f")))) && (a1729378197 == 6))) {
    	cf = false;
    	a1477849038 = "h";
    	a1114110175 = "e";
    	a1729378197 = 4; 
    	System.out.println("R");
    } if(((input.equals("K")) && ((a1047798024.equals("e")) && ((cf && (a1729378197 == 6)) && (a1583272058.equals("f")))))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 8;
    	a1853964249 = 5; 
    	System.out.println("P");
    } if((((((a1729378197 == 6) && cf) && (a1047798024.equals("e"))) && (a1583272058.equals("f"))) && (input.equals("M")))) {
    	cf = false;
    	a938681481 = 10;
    	a1729378197 = 1;
    	a198422080 = 11; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm215(String input) {
    if((((((a1047798024.equals("e")) && cf) && (input.equals("J"))) && (a1729378197 == 6)) && (a1583272058.equals("h")))) {
    	cf = false;
    	a23351479 = 11;
    	a1729378197 = 5;
    	a520438996 = 5; 
    	System.out.println("P");
    } if(((a1583272058.equals("h")) && (((a1729378197 == 6) && ((a1047798024.equals("e")) && cf)) && (input.equals("O"))))) {
    	cf = false;
    	a1466114073 = "h";
    	a1729378197 = 1;
    	a938681481 = 6; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm32(String input) {
    if(((a1583272058.equals("f")) && cf)) {
    	calculateOutputm214(input);
    } 
    if((cf && (a1583272058.equals("h")))) {
    	calculateOutputm215(input);
    } 
}
private  void calculateOutputm217(String input) {
    if((((a1729378197 == 6) && ((input.equals("G")) && (cf && (a24442901.equals("e"))))) && (a1047798024.equals("f")))) {
    	cf = false;
    	a1245641101 = "h";
    	a1729378197 = 7;
    	a1920565083 = 10; 
    	System.out.println("R");
    } 
}
private  void calculateOutputm218(String input) {
    if(((((cf && (input.equals("F"))) && (a1047798024.equals("f"))) && (a1729378197 == 6)) && (a24442901.equals("f")))) {
    	cf = false;
    	a1584317767 = "f";
    	a1477849038 = "g";
    	a1729378197 = 4; 
    	System.out.println("U");
    } if(((a1047798024.equals("f")) && (((a1729378197 == 6) && ((input.equals("O")) && cf)) && (a24442901.equals("f"))))) {
    	cf = false;
    	a1729378197 = 8;
    	a299375216 = 4;
    	a1105418891 = 8; 
    	System.out.println("V");
    } 
}
private  void calculateOutputm220(String input) {
    if(((a1047798024.equals("f")) && ((a1729378197 == 6) && ((input.equals("H")) && ((a24442901.equals("h")) && cf))))) {
    	cf = false;
    	a583157892 = "f";
    	a1729378197 = 5;
    	a23351479 = 16; 
    	System.out.println("V");
    } 
}
private  void calculateOutputm221(String input) {
    if((((input.equals("J")) && ((cf && (a1047798024.equals("f"))) && (a1729378197 == 6))) && (a24442901.equals("i")))) {
    	cf = false;
    	a1729378197 = 2;
    	a1477849038 = "g";
    	a541989745 = 8; 
    	System.out.println("V");
    } 
}
private  void calculateOutputm33(String input) {
    if(((a24442901.equals("e")) && cf)) {
    	calculateOutputm217(input);
    } 
    if((cf && (a24442901.equals("f")))) {
    	calculateOutputm218(input);
    } 
    if(((a24442901.equals("h")) && cf)) {
    	calculateOutputm220(input);
    } 
    if((cf && (a24442901.equals("i")))) {
    	calculateOutputm221(input);
    } 
}
private  void calculateOutputm222(String input) {
    if(((input.equals("A")) && ((a1047798024.equals("g")) && (((a1729378197 == 6) && cf) && (a23351479 == 10))))) {
    	cf = false;
    	a1729378197 = 8;
    	a299375216 = 4;
    	a1105418891 = 9; 
    	System.out.println("S");
    } if((((((a23351479 == 10) && cf) && (a1729378197 == 6)) && (input.equals("J"))) && (a1047798024.equals("g")))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 8;
    	a1853964249 = 6; 
    	System.out.println("V");
    } if((((a1047798024.equals("g")) && (((input.equals("K")) && cf) && (a23351479 == 10))) && (a1729378197 == 6))) {
    	cf = false;
    	a1729378197 = 5;
    	a37252965 = 13; 
    	System.out.println("T");
    } if((((input.equals("M")) && (((a1047798024.equals("g")) && cf) && (a1729378197 == 6))) && (a23351479 == 10))) {
    	cf = false;
    	a839019366 = "f";
    	a1729378197 = 5;
    	a23351479 = 13; 
    	System.out.println("S");
    } if((((input.equals("E")) && (((a1729378197 == 6) && cf) && (a23351479 == 10))) && (a1047798024.equals("g")))) {
    	cf = false;
    	a1716858626 = "i";
    	a1477849038 = "e";
    	a1729378197 = 4; 
    	System.out.println("X");
    } 
}
private  void calculateOutputm224(String input) {
    if(((a1047798024.equals("g")) && ((a23351479 == 13) && (((input.equals("C")) && cf) && (a1729378197 == 6))))) {
    	cf = false;
    	a1114110175 = "i";
    	a1477849038 = "h";
    	a1729378197 = 4; 
    	System.out.println("Z");
    } if(((a23351479 == 13) && ((input.equals("H")) && (((a1729378197 == 6) && cf) && (a1047798024.equals("g")))))) {
    	cf = false;
    	a1937499914 = "f";
    	a1729378197 = 1;
    	a938681481 = 13; 
    	System.out.println("Q");
    } if((((input.equals("O")) && ((a1729378197 == 6) && (cf && (a23351479 == 13)))) && (a1047798024.equals("g")))) {
    	cf = false;
    	a1937499914 = "f";
    	a1729378197 = 1;
    	a938681481 = 13; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm225(String input) {
    if(((((a23351479 == 14) && ((a1729378197 == 6) && cf)) && (a1047798024.equals("g"))) && (input.equals("C")))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 7;
    	a1716763601 = 5; 
    	System.out.println("Y");
    } if(((a1047798024.equals("g")) && ((a23351479 == 14) && ((cf && (input.equals("H"))) && (a1729378197 == 6))))) {
    	cf = false;
    	 
    	System.out.println("S");
    } if(((a23351479 == 14) && ((a1047798024.equals("g")) && ((input.equals("J")) && (cf && (a1729378197 == 6)))))) {
    	cf = false;
    	a648437939 = "h";
    	a1477849038 = "h";
    	a1729378197 = 2; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm226(String input) {
    if(((((cf && (a1729378197 == 6)) && (input.equals("C"))) && (a23351479 == 15)) && (a1047798024.equals("g")))) {
    	cf = false;
    	a1477849038 = "e";
    	a1716858626 = "f";
    	a1729378197 = 4; 
    	System.out.println("R");
    } if(((input.equals("D")) && ((a23351479 == 15) && ((a1047798024.equals("g")) && ((a1729378197 == 6) && cf))))) {
    	cf = false;
    	a1047798024 = "f";
    	a24442901 = "i"; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm34(String input) {
    if(((a23351479 == 10) && cf)) {
    	calculateOutputm222(input);
    } 
    if(((a23351479 == 13) && cf)) {
    	calculateOutputm224(input);
    } 
    if(((a23351479 == 14) && cf)) {
    	calculateOutputm225(input);
    } 
    if((cf && (a23351479 == 15))) {
    	calculateOutputm226(input);
    } 
}
private  void calculateOutputm228(String input) {
    if(((input.equals("A")) && ((a1729378197 == 6) && ((cf && (a1047798024.equals("h"))) && (a274626616.equals("f")))))) {
    	cf = false;
    	a1716858626 = "e";
    	a1477849038 = "e";
    	a1729378197 = 4; 
    	System.out.println("U");
    } if((((a1729378197 == 6) && ((cf && (input.equals("D"))) && (a274626616.equals("f")))) && (a1047798024.equals("h")))) {
    	cf = false;
    	a366362113 = "i";
    	a123124249 = "i";
    	a1729378197 = 3; 
    	System.out.println("P");
    } if(((a274626616.equals("f")) && ((a1047798024.equals("h")) && ((cf && (a1729378197 == 6)) && (input.equals("F")))))) {
    	cf = false;
    	a938681481 = 10;
    	a1729378197 = 1;
    	a198422080 = 10; 
    	System.out.println("W");
    } 
}
private  void calculateOutputm229(String input) {
    if(((a1729378197 == 6) && ((((a274626616.equals("h")) && cf) && (input.equals("A"))) && (a1047798024.equals("h"))))) {
    	cf = false;
    	a1477849038 = "h";
    	a648437939 = "g";
    	a1729378197 = 2; 
    	System.out.println("T");
    } if(((a274626616.equals("h")) && ((a1729378197 == 6) && ((a1047798024.equals("h")) && ((input.equals("B")) && cf))))) {
    	cf = false;
    	a23351479 = 10;
    	a1729378197 = 5;
    	a37252965 = 10; 
    	System.out.println("R");
    } if(((a1047798024.equals("h")) && ((input.equals("J")) && ((a274626616.equals("h")) && (cf && (a1729378197 == 6)))))) {
    	cf = false;
    	a1570444282 = "f";
    	a1477849038 = "f";
    	a1729378197 = 4; 
    	System.out.println("Z");
    } if(((((a1047798024.equals("h")) && (cf && (a1729378197 == 6))) && (input.equals("K"))) && (a274626616.equals("h")))) {
    	cf = false;
    	a1729378197 = 8;
    	a853421711 = "h";
    	a299375216 = 8; 
    	System.out.println("X");
    } 
}
private  void calculateOutputm230(String input) {
    if(((a274626616.equals("i")) && (((cf && (input.equals("C"))) && (a1729378197 == 6)) && (a1047798024.equals("h"))))) {
    	cf = false;
    	a938681481 = 10;
    	a1729378197 = 1;
    	a198422080 = 12; 
    	System.out.println("W");
    } if(((((input.equals("D")) && (cf && (a1729378197 == 6))) && (a1047798024.equals("h"))) && (a274626616.equals("i")))) {
    	cf = false;
    	a1729378197 = 5;
    	a839019366 = "f";
    	a23351479 = 13; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm35(String input) {
    if(((a274626616.equals("f")) && cf)) {
    	calculateOutputm228(input);
    } 
    if((cf && (a274626616.equals("h")))) {
    	calculateOutputm229(input);
    } 
    if((cf && (a274626616.equals("i")))) {
    	calculateOutputm230(input);
    } 
}
private  void calculateOutputm231(String input) {
    if(((a911974320.equals("e")) && (((a1729378197 == 6) && ((a1047798024.equals("i")) && cf)) && (input.equals("F"))))) {
    	cf = false;
    	a674877 = "e";
    	a1477849038 = "e";
    	a1729378197 = 2; 
    	System.out.println("S");
    } if((((input.equals("H")) && (((a911974320.equals("e")) && cf) && (a1047798024.equals("i")))) && (a1729378197 == 6))) {
    	cf = false;
    	a1477849038 = "e";
    	a674877 = "e";
    	a1729378197 = 2; 
    	System.out.println("S");
    } if((((((a1047798024.equals("i")) && cf) && (a911974320.equals("e"))) && (a1729378197 == 6)) && (input.equals("J")))) {
    	cf = false;
    	a1920565083 = 13;
    	a1729378197 = 7;
    	a1518235786 = 5; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm232(String input) {
    if(((input.equals("G")) && (((a1729378197 == 6) && ((a911974320.equals("f")) && cf)) && (a1047798024.equals("i"))))) {
    	cf = false;
    	a938681481 = 11;
    	a1729378197 = 1;
    	a1892947393 = 5; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm233(String input) {
    if((((a1047798024.equals("i")) && ((a911974320.equals("g")) && (cf && (a1729378197 == 6)))) && (input.equals("C")))) {
    	cf = false;
    	a1477849038 = "f";
    	a1570444282 = "g";
    	a1729378197 = 4; 
    	System.out.println("X");
    } if((((a1047798024.equals("i")) && (((input.equals("H")) && cf) && (a1729378197 == 6))) && (a911974320.equals("g")))) {
    	cf = false;
    	a23351479 = 14;
    	a1729378197 = 5;
    	a871304185 = 7; 
    	System.out.println("R");
    } if((((input.equals("L")) && (((a911974320.equals("g")) && cf) && (a1047798024.equals("i")))) && (a1729378197 == 6))) {
    	cf = false;
    	a23351479 = 15;
    	a1729378197 = 5;
    	a948298434 = 9; 
    	System.out.println("R");
    } 
}
private  void calculateOutputm235(String input) {
    if(((((a1729378197 == 6) && ((a1047798024.equals("i")) && cf)) && (input.equals("J"))) && (a911974320.equals("i")))) {
    	cf = false;
    	a625366011 = "e";
    	a1477849038 = "f";
    	a1729378197 = 2; 
    	System.out.println("W");
    } if(((a911974320.equals("i")) && ((a1047798024.equals("i")) && ((input.equals("L")) && (cf && (a1729378197 == 6)))))) {
    	cf = false;
    	 
    	System.out.println("U");
    } 
}
private  void calculateOutputm36(String input) {
    if(((a911974320.equals("e")) && cf)) {
    	calculateOutputm231(input);
    } 
    if(((a911974320.equals("f")) && cf)) {
    	calculateOutputm232(input);
    } 
    if((cf && (a911974320.equals("g")))) {
    	calculateOutputm233(input);
    } 
    if((cf && (a911974320.equals("i")))) {
    	calculateOutputm235(input);
    } 
}
private  void calculateOutputm236(String input) {
    if((((a1668586383 == 2) && (((input.equals("H")) && cf) && (a1729378197 == 7))) && (a1920565083 == 8))) {
    	cf = false;
    	a1729378197 = 5;
    	a23351479 = 15;
    	a948298434 = 7; 
    	System.out.println("U");
    } if(((a1668586383 == 2) && ((input.equals("M")) && ((cf && (a1920565083 == 8)) && (a1729378197 == 7))))) {
    	cf = false;
    	a938681481 = 11;
    	a1729378197 = 1;
    	a1892947393 = 8; 
    	System.out.println("X");
    } 
}
private  void calculateOutputm237(String input) {
    if(((input.equals("A")) && ((a1668586383 == 3) && ((a1920565083 == 8) && (cf && (a1729378197 == 7)))))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 12;
    	a1075056448 = 6; 
    	System.out.println("W");
    } if((((((a1920565083 == 8) && cf) && (input.equals("O"))) && (a1729378197 == 7)) && (a1668586383 == 3))) {
    	cf = false;
    	a911974320 = "e";
    	a1047798024 = "i";
    	a1729378197 = 6; 
    	System.out.println("W");
    } 
}
private  void calculateOutputm241(String input) {
    if((((a1729378197 == 7) && ((input.equals("B")) && (cf && (a1668586383 == 7)))) && (a1920565083 == 8))) {
    	cf = false;
    	 
    	System.out.println("S");
    } if(((((input.equals("K")) && ((a1729378197 == 7) && cf)) && (a1668586383 == 7)) && (a1920565083 == 8))) {
    	cf = false;
    	a1729378197 = 8;
    	a299375216 = 3;
    	a310220227 = 11; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm37(String input) {
    if(((a1668586383 == 2) && cf)) {
    	calculateOutputm236(input);
    } 
    if(((a1668586383 == 3) && cf)) {
    	calculateOutputm237(input);
    } 
    if((cf && (a1668586383 == 7))) {
    	calculateOutputm241(input);
    } 
}
private  void calculateOutputm244(String input) {
    if(((((a650861711.equals("f")) && ((a1729378197 == 7) && cf)) && (input.equals("F"))) && (a1920565083 == 9))) {
    	cf = false;
    	a1477849038 = "h";
    	a1114110175 = "i";
    	a1729378197 = 4; 
    	System.out.println("Z");
    } if(((a650861711.equals("f")) && (((cf && (a1729378197 == 7)) && (a1920565083 == 9)) && (input.equals("H"))))) {
    	cf = false;
    	a299375216 = 3;
    	a1729378197 = 8;
    	a310220227 = 14; 
    	System.out.println("W");
    } if((((a1920565083 == 9) && ((input.equals("L")) && (cf && (a1729378197 == 7)))) && (a650861711.equals("f")))) {
    	cf = false;
    	a299375216 = 3;
    	a1729378197 = 8;
    	a310220227 = 11; 
    	System.out.println("T");
    } if(((a650861711.equals("f")) && ((a1920565083 == 9) && ((input.equals("M")) && ((a1729378197 == 7) && cf))))) {
    	cf = false;
    	a1729378197 = 8;
    	a299375216 = 3;
    	a310220227 = 11; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm246(String input) {
    if(((a1920565083 == 9) && (((a650861711.equals("i")) && ((input.equals("C")) && cf)) && (a1729378197 == 7)))) {
    	cf = false;
    	a1729378197 = 4;
    	a1477849038 = "i";
    	a50296898 = 10; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm38(String input) {
    if((cf && (a650861711.equals("f")))) {
    	calculateOutputm244(input);
    } 
    if((cf && (a650861711.equals("i")))) {
    	calculateOutputm246(input);
    } 
}
private  void calculateOutputm247(String input) {
    if(((a1729378197 == 7) && ((a1920565083 == 10) && ((a1245641101.equals("e")) && (cf && (input.equals("G"))))))) {
    	cf = false;
    	a1584317767 = "i";
    	a1477849038 = "g";
    	a1729378197 = 4; 
    	System.out.println("S");
    } if(((input.equals("H")) && ((((a1729378197 == 7) && cf) && (a1920565083 == 10)) && (a1245641101.equals("e"))))) {
    	cf = false;
    	a68550605 = "i";
    	a1920565083 = 14; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm248(String input) {
    if(((a1245641101.equals("f")) && ((a1920565083 == 10) && ((a1729378197 == 7) && ((input.equals("C")) && cf))))) {
    	cf = false;
    	a123124249 = "h";
    	a1729378197 = 3;
    	a198422080 = 6; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm249(String input) {
    if(((a1729378197 == 7) && ((a1920565083 == 10) && ((cf && (input.equals("A"))) && (a1245641101.equals("g")))))) {
    	cf = false;
    	a625366011 = "i";
    	a1477849038 = "f";
    	a1729378197 = 2; 
    	System.out.println("W");
    } if((((a1245641101.equals("g")) && ((input.equals("K")) && (cf && (a1729378197 == 7)))) && (a1920565083 == 10))) {
    	cf = false;
    	a1729378197 = 8;
    	a299375216 = 4;
    	a1105418891 = 13; 
    	System.out.println("T");
    } if(((((cf && (a1245641101.equals("g"))) && (a1920565083 == 10)) && (a1729378197 == 7)) && (input.equals("O")))) {
    	cf = false;
    	a648437939 = "i";
    	a1477849038 = "h";
    	a1729378197 = 2; 
    	System.out.println("Y");
    } if(((((input.equals("C")) && (cf && (a1245641101.equals("g")))) && (a1920565083 == 10)) && (a1729378197 == 7))) {
    	cf = false;
    	a23351479 = 15;
    	a1729378197 = 5;
    	a948298434 = 8; 
    	System.out.println("X");
    } 
}
private  void calculateOutputm250(String input) {
    if(((a1729378197 == 7) && ((a1920565083 == 10) && ((a1245641101.equals("h")) && ((input.equals("O")) && cf))))) {
    	cf = false;
    	a1477849038 = "g";
    	a1729378197 = 2;
    	a541989745 = 10; 
    	System.out.println("U");
    } if(((a1729378197 == 7) && ((a1920565083 == 10) && ((a1245641101.equals("h")) && ((input.equals("G")) && cf))))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 10;
    	a198422080 = 9; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm251(String input) {
    if(((input.equals("A")) && ((((a1245641101.equals("i")) && cf) && (a1729378197 == 7)) && (a1920565083 == 10)))) {
    	cf = false;
    	a68550605 = "f";
    	a1920565083 = 14; 
    	System.out.println("S");
    } if((((((input.equals("F")) && cf) && (a1729378197 == 7)) && (a1245641101.equals("i"))) && (a1920565083 == 10))) {
    	cf = false;
    	a366362113 = "i";
    	a123124249 = "i";
    	a1729378197 = 3; 
    	System.out.println("X");
    } if(((a1729378197 == 7) && ((input.equals("M")) && ((a1920565083 == 10) && ((a1245641101.equals("i")) && cf))))) {
    	cf = false;
    	a123124249 = "g";
    	a1729378197 = 3;
    	a1091978491 = 11; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm39(String input) {
    if(((a1245641101.equals("e")) && cf)) {
    	calculateOutputm247(input);
    } 
    if((cf && (a1245641101.equals("f")))) {
    	calculateOutputm248(input);
    } 
    if(((a1245641101.equals("g")) && cf)) {
    	calculateOutputm249(input);
    } 
    if(((a1245641101.equals("h")) && cf)) {
    	calculateOutputm250(input);
    } 
    if((cf && (a1245641101.equals("i")))) {
    	calculateOutputm251(input);
    } 
}
private  void calculateOutputm253(String input) {
    if(((((a312388145 == 8) && ((a1920565083 == 11) && cf)) && (a1729378197 == 7)) && (input.equals("A")))) {
    	cf = false;
    	a274626616 = "f";
    	a1047798024 = "h";
    	a1729378197 = 6; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm255(String input) {
    if(((a312388145 == 10) && ((a1729378197 == 7) && ((a1920565083 == 11) && (cf && (input.equals("J"))))))) {
    	cf = false;
    	a1729378197 = 5;
    	a23351479 = 11;
    	a520438996 = 11; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm40(String input) {
    if(((a312388145 == 8) && cf)) {
    	calculateOutputm253(input);
    } 
    if((cf && (a312388145 == 10))) {
    	calculateOutputm255(input);
    } 
}
private  void calculateOutputm257(String input) {
    if((((input.equals("C")) && ((a1729378197 == 7) && (cf && (a1920565083 == 12)))) && (a750845785.equals("e")))) {
    	cf = false;
    	a938681481 = 12;
    	a1729378197 = 1;
    	a1075056448 = 7; 
    	System.out.println("U");
    } if(((a750845785.equals("e")) && ((input.equals("M")) && ((a1920565083 == 12) && ((a1729378197 == 7) && cf))))) {
    	cf = false;
    	a1729378197 = 6;
    	a1047798024 = "g";
    	a23351479 = 13; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm258(String input) {
    if(((input.equals("G")) && (((a1729378197 == 7) && (cf && (a1920565083 == 12))) && (a750845785.equals("f"))))) {
    	cf = false;
    	a1729378197 = 8;
    	a847841994 = "f";
    	a299375216 = 1; 
    	System.out.println("S");
    } if(((((a1729378197 == 7) && (cf && (a1920565083 == 12))) && (input.equals("H"))) && (a750845785.equals("f")))) {
    	cf = false;
    	a1937499914 = "f";
    	a1729378197 = 1;
    	a938681481 = 13; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm259(String input) {
    if(((input.equals("H")) && (((a750845785.equals("i")) && (cf && (a1920565083 == 12))) && (a1729378197 == 7)))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 12;
    	a1075056448 = 12; 
    	System.out.println("Q");
    } if(((((cf && (a1920565083 == 12)) && (a1729378197 == 7)) && (a750845785.equals("i"))) && (input.equals("K")))) {
    	cf = false;
    	a1583272058 = "f";
    	a1047798024 = "e";
    	a1729378197 = 6; 
    	System.out.println("X");
    } if(((a750845785.equals("i")) && ((input.equals("M")) && ((a1729378197 == 7) && ((a1920565083 == 12) && cf))))) {
    	cf = false;
    	a1920565083 = 8;
    	a1668586383 = 3; 
    	System.out.println("V");
    } if(((a1920565083 == 12) && ((((a1729378197 == 7) && cf) && (input.equals("F"))) && (a750845785.equals("i"))))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 7;
    	a1716763601 = 10; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm41(String input) {
    if((cf && (a750845785.equals("e")))) {
    	calculateOutputm257(input);
    } 
    if(((a750845785.equals("f")) && cf)) {
    	calculateOutputm258(input);
    } 
    if((cf && (a750845785.equals("i")))) {
    	calculateOutputm259(input);
    } 
}
private  void calculateOutputm260(String input) {
    if((((a1729378197 == 7) && (((a1920565083 == 13) && cf) && (input.equals("A")))) && (a1518235786 == 5))) {
    	cf = false;
    	a1114110175 = "i";
    	a1477849038 = "h";
    	a1729378197 = 4; 
    	System.out.println("Z");
    } if(((a1920565083 == 13) && (((input.equals("F")) && ((a1518235786 == 5) && cf)) && (a1729378197 == 7)))) {
    	cf = false;
    	 
    	System.out.println("X");
    } if(((input.equals("G")) && (((cf && (a1920565083 == 13)) && (a1729378197 == 7)) && (a1518235786 == 5)))) {
    	cf = false;
    	a1477849038 = "h";
    	a1114110175 = "i";
    	a1729378197 = 4; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm261(String input) {
    if(((a1518235786 == 6) && (((input.equals("B")) && (cf && (a1920565083 == 13))) && (a1729378197 == 7)))) {
    	cf = false;
    	a938681481 = 11;
    	a1729378197 = 1;
    	a1892947393 = 9; 
    	System.out.println("U");
    } if(((input.equals("M")) && (((a1729378197 == 7) && ((a1920565083 == 13) && cf)) && (a1518235786 == 6)))) {
    	cf = false;
    	a847841994 = "f";
    	a1729378197 = 8;
    	a299375216 = 1; 
    	System.out.println("S");
    } if(((a1920565083 == 13) && (((input.equals("O")) && (cf && (a1729378197 == 7))) && (a1518235786 == 6)))) {
    	cf = false;
    	a1729378197 = 8;
    	a1047798024 = "g";
    	a299375216 = 2; 
    	System.out.println("Q");
    } if((((a1518235786 == 6) && ((cf && (input.equals("D"))) && (a1920565083 == 13))) && (a1729378197 == 7))) {
    	cf = false;
    	a1920565083 = 8;
    	a1668586383 = 9; 
    	System.out.println("W");
    } 
}
private  void calculateOutputm262(String input) {
    if(((a1920565083 == 13) && ((a1518235786 == 7) && ((input.equals("D")) && ((a1729378197 == 7) && cf))))) {
    	cf = false;
    	a938681481 = 11;
    	a1729378197 = 1;
    	a1892947393 = 10; 
    	System.out.println("X");
    } if(((((a1729378197 == 7) && (cf && (a1518235786 == 7))) && (input.equals("L"))) && (a1920565083 == 13))) {
    	cf = false;
    	a23351479 = 10;
    	a1729378197 = 5;
    	a37252965 = 8; 
    	System.out.println("P");
    } if(((input.equals("J")) && ((a1729378197 == 7) && ((cf && (a1518235786 == 7)) && (a1920565083 == 13))))) {
    	cf = false;
    	a1920565083 = 8;
    	a1668586383 = 4; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm264(String input) {
    if(((a1920565083 == 13) && ((input.equals("B")) && (((a1518235786 == 9) && cf) && (a1729378197 == 7))))) {
    	cf = false;
    	a299375216 = 3;
    	a1729378197 = 8;
    	a310220227 = 12; 
    	System.out.println("U");
    } if(((a1518235786 == 9) && (((cf && (a1729378197 == 7)) && (input.equals("C"))) && (a1920565083 == 13)))) {
    	cf = false;
    	a274626616 = "h";
    	a1047798024 = "h";
    	a1729378197 = 6; 
    	System.out.println("T");
    } if(((a1518235786 == 9) && (((input.equals("H")) && ((a1920565083 == 13) && cf)) && (a1729378197 == 7)))) {
    	cf = false;
    	a1245641101 = "g";
    	a1920565083 = 10; 
    	System.out.println("Z");
    } if((((input.equals("J")) && ((a1518235786 == 9) && ((a1729378197 == 7) && cf))) && (a1920565083 == 13))) {
    	cf = false;
    	a123124249 = "h";
    	a1729378197 = 3;
    	a198422080 = 7; 
    	System.out.println("P");
    } if((((a1920565083 == 13) && ((cf && (a1729378197 == 7)) && (input.equals("A")))) && (a1518235786 == 9))) {
    	cf = false;
    	a520547452 = "g";
    	a1477849038 = "i";
    	a1729378197 = 2; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm265(String input) {
    if((((input.equals("A")) && ((a1518235786 == 10) && ((a1729378197 == 7) && cf))) && (a1920565083 == 13))) {
    	cf = false;
    	a1477849038 = "h";
    	a1114110175 = "i";
    	a1729378197 = 4; 
    	System.out.println("Z");
    } if(((a1518235786 == 10) && ((a1729378197 == 7) && ((a1920565083 == 13) && (cf && (input.equals("C"))))))) {
    	cf = false;
    	a1729378197 = 1;
    	a1937499914 = "i";
    	a938681481 = 13; 
    	System.out.println("Z");
    } if(((((cf && (input.equals("H"))) && (a1920565083 == 13)) && (a1518235786 == 10)) && (a1729378197 == 7))) {
    	cf = false;
    	a1937499914 = "f";
    	a1729378197 = 1;
    	a938681481 = 13; 
    	System.out.println("Q");
    } if((((a1518235786 == 10) && ((input.equals("K")) && ((a1920565083 == 13) && cf))) && (a1729378197 == 7))) {
    	cf = false;
    	a1729378197 = 1;
    	a1937499914 = "i";
    	a938681481 = 13; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm42(String input) {
    if(((a1518235786 == 5) && cf)) {
    	calculateOutputm260(input);
    } 
    if(((a1518235786 == 6) && cf)) {
    	calculateOutputm261(input);
    } 
    if((cf && (a1518235786 == 7))) {
    	calculateOutputm262(input);
    } 
    if((cf && (a1518235786 == 9))) {
    	calculateOutputm264(input);
    } 
    if((cf && (a1518235786 == 10))) {
    	calculateOutputm265(input);
    } 
}
private  void calculateOutputm269(String input) {
    if((((input.equals("A")) && ((cf && (a68550605.equals("f"))) && (a1920565083 == 14))) && (a1729378197 == 7))) {
    	cf = false;
    	a1729378197 = 1;
    	a1937499914 = "f";
    	a938681481 = 13; 
    	System.out.println("Q");
    } if(((input.equals("C")) && ((a68550605.equals("f")) && ((a1729378197 == 7) && (cf && (a1920565083 == 14)))))) {
    	cf = false;
    	a1245641101 = "h";
    	a1920565083 = 10; 
    	System.out.println("W");
    } if((((input.equals("D")) && ((a1920565083 == 14) && (cf && (a1729378197 == 7)))) && (a68550605.equals("f")))) {
    	cf = false;
    	 
    	System.out.println("S");
    } if(((((a1920565083 == 14) && ((input.equals("G")) && cf)) && (a68550605.equals("f"))) && (a1729378197 == 7))) {
    	cf = false;
    	a1245641101 = "i";
    	a1920565083 = 10; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm271(String input) {
    if(((((cf && (a1920565083 == 14)) && (input.equals("B"))) && (a1729378197 == 7)) && (a68550605.equals("h")))) {
    	cf = false;
    	a1047798024 = "g";
    	a1729378197 = 6;
    	a23351479 = 14; 
    	System.out.println("S");
    } if(((input.equals("J")) && (((a1920565083 == 14) && (cf && (a1729378197 == 7))) && (a68550605.equals("h"))))) {
    	cf = false;
    	a366362113 = "h";
    	a123124249 = "i";
    	a1729378197 = 3; 
    	System.out.println("Y");
    } if(((a68550605.equals("h")) && (((cf && (a1920565083 == 14)) && (a1729378197 == 7)) && (input.equals("L"))))) {
    	cf = false;
    	a1920565083 = 13;
    	a1518235786 = 9; 
    	System.out.println("W");
    } 
}
private  void calculateOutputm272(String input) {
    if((((a68550605.equals("i")) && ((a1729378197 == 7) && (cf && (input.equals("B"))))) && (a1920565083 == 14))) {
    	cf = false;
    	a1937499914 = "i";
    	a1729378197 = 1;
    	a938681481 = 13; 
    	System.out.println("Z");
    } if(((((a1729378197 == 7) && (cf && (input.equals("D")))) && (a1920565083 == 14)) && (a68550605.equals("i")))) {
    	cf = false;
    	 
    	System.out.println("U");
    } if((((a1920565083 == 14) && ((input.equals("H")) && ((a1729378197 == 7) && cf))) && (a68550605.equals("i")))) {
    	cf = false;
    	a1477849038 = "h";
    	a1114110175 = "i";
    	a1729378197 = 4; 
    	System.out.println("Z");
    } if((((a1729378197 == 7) && (((input.equals("K")) && cf) && (a68550605.equals("i")))) && (a1920565083 == 14))) {
    	cf = false;
    	a1937499914 = "i";
    	a1729378197 = 1;
    	a938681481 = 13; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm43(String input) {
    if(((a68550605.equals("f")) && cf)) {
    	calculateOutputm269(input);
    } 
    if((cf && (a68550605.equals("h")))) {
    	calculateOutputm271(input);
    } 
    if(((a68550605.equals("i")) && cf)) {
    	calculateOutputm272(input);
    } 
}
private  void calculateOutputm277(String input) {
    if((((a1920565083 == 15) && ((a1105418891 == 12) && (cf && (a1729378197 == 7)))) && (input.equals("D")))) {
    	cf = false;
    	a650861711 = "f";
    	a1920565083 = 9; 
    	System.out.println("V");
    } if(((input.equals("M")) && ((((a1729378197 == 7) && cf) && (a1105418891 == 12)) && (a1920565083 == 15)))) {
    	cf = false;
    	a1920565083 = 13;
    	a1518235786 = 5; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm44(String input) {
    if(((a1105418891 == 12) && cf)) {
    	calculateOutputm277(input);
    } 
}
private  void calculateOutputm279(String input) {
    if(((a847841994.equals("f")) && ((a1729378197 == 8) && (((input.equals("C")) && cf) && (a299375216 == 1))))) {
    	cf = false;
    	a1306585414 = "g";
    	a299375216 = 7; 
    	System.out.println("P");
    } if((((a1729378197 == 8) && ((a299375216 == 1) && (cf && (input.equals("F"))))) && (a847841994.equals("f")))) {
    	cf = false;
    	a1729378197 = 7;
    	a750845785 = "f";
    	a1920565083 = 12; 
    	System.out.println("U");
    } if(((((a847841994.equals("f")) && (cf && (a1729378197 == 8))) && (input.equals("G"))) && (a299375216 == 1))) {
    	cf = false;
    	a1477849038 = "e";
    	a1716858626 = "e";
    	a1729378197 = 4; 
    	System.out.println("U");
    } if(((input.equals("M")) && (((cf && (a847841994.equals("f"))) && (a1729378197 == 8)) && (a299375216 == 1)))) {
    	cf = false;
    	a1584317767 = "i";
    	a1477849038 = "g";
    	a1729378197 = 4; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm280(String input) {
    if((((a299375216 == 1) && ((input.equals("J")) && (cf && (a1729378197 == 8)))) && (a847841994.equals("g")))) {
    	cf = false;
    	a1477849038 = "e";
    	a674877 = "f";
    	a1729378197 = 2; 
    	System.out.println("S");
    } if(((((a1729378197 == 8) && (cf && (input.equals("M")))) && (a299375216 == 1)) && (a847841994.equals("g")))) {
    	cf = false;
    	a1584317767 = "i";
    	a123124249 = "f";
    	a1729378197 = 3; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm281(String input) {
    if(((a1729378197 == 8) && (((cf && (a847841994.equals("h"))) && (a299375216 == 1)) && (input.equals("D"))))) {
    	cf = false;
    	a299375216 = 4;
    	a1105418891 = 10; 
    	System.out.println("T");
    } if(((a299375216 == 1) && (((a1729378197 == 8) && (cf && (a847841994.equals("h")))) && (input.equals("G"))))) {
    	cf = false;
    	a1039409491 = "i";
    	a299375216 = 6; 
    	System.out.println("W");
    } if((((a1729378197 == 8) && ((a299375216 == 1) && (cf && (a847841994.equals("h"))))) && (input.equals("L")))) {
    	cf = false;
    	a1729378197 = 5;
    	a23351479 = 12;
    	a1803458941 = 17; 
    	System.out.println("Z");
    } if((((((a847841994.equals("h")) && cf) && (input.equals("O"))) && (a299375216 == 1)) && (a1729378197 == 8))) {
    	cf = false;
    	a938681481 = 8;
    	a1729378197 = 1;
    	a1853964249 = 7; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm282(String input) {
    if(((a847841994.equals("i")) && (((input.equals("F")) && ((a299375216 == 1) && cf)) && (a1729378197 == 8)))) {
    	cf = false;
    	a1114110175 = "i";
    	a1477849038 = "h";
    	a1729378197 = 4; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm45(String input) {
    if((cf && (a847841994.equals("f")))) {
    	calculateOutputm279(input);
    } 
    if(((a847841994.equals("g")) && cf)) {
    	calculateOutputm280(input);
    } 
    if(((a847841994.equals("h")) && cf)) {
    	calculateOutputm281(input);
    } 
    if(((a847841994.equals("i")) && cf)) {
    	calculateOutputm282(input);
    } 
}
private  void calculateOutputm284(String input) {
    if((((a1047798024.equals("f")) && ((a299375216 == 2) && (cf && (input.equals("C"))))) && (a1729378197 == 8))) {
    	cf = false;
    	a1245641101 = "f";
    	a1729378197 = 7;
    	a1920565083 = 10; 
    	System.out.println("S");
    } if(((a1047798024.equals("f")) && ((a299375216 == 2) && ((input.equals("H")) && ((a1729378197 == 8) && cf))))) {
    	cf = false;
    	a1729378197 = 3;
    	a123124249 = "g";
    	a1091978491 = 11; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm285(String input) {
    if((((a299375216 == 2) && ((a1047798024.equals("g")) && (cf && (input.equals("A"))))) && (a1729378197 == 8))) {
    	cf = false;
    	a847841994 = "i";
    	a299375216 = 1; 
    	System.out.println("U");
    } if((((a1047798024.equals("g")) && (((input.equals("C")) && cf) && (a299375216 == 2))) && (a1729378197 == 8))) {
    	cf = false;
    	a1039409491 = "e";
    	a299375216 = 6; 
    	System.out.println("U");
    } if(((a1729378197 == 8) && ((((a1047798024.equals("g")) && cf) && (input.equals("O"))) && (a299375216 == 2)))) {
    	cf = false;
    	a123124249 = "f";
    	a1584317767 = "i";
    	a1729378197 = 3; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm286(String input) {
    if(((a299375216 == 2) && ((a1047798024.equals("h")) && ((a1729378197 == 8) && ((input.equals("G")) && cf))))) {
    	cf = false;
    	a1047798024 = "f"; 
    	System.out.println("V");
    } 
}
private  void calculateOutputm46(String input) {
    if(((a1047798024.equals("f")) && cf)) {
    	calculateOutputm284(input);
    } 
    if((cf && (a1047798024.equals("g")))) {
    	calculateOutputm285(input);
    } 
    if(((a1047798024.equals("h")) && cf)) {
    	calculateOutputm286(input);
    } 
}
private  void calculateOutputm288(String input) {
    if(((input.equals("A")) && ((a299375216 == 3) && ((a1729378197 == 8) && (cf && (a310220227 == 7)))))) {
    	cf = false;
    	a938681481 = 11;
    	a1729378197 = 1;
    	a1892947393 = 9; 
    	System.out.println("U");
    } if((((a1729378197 == 8) && ((a299375216 == 3) && (cf && (a310220227 == 7)))) && (input.equals("J")))) {
    	cf = false;
    	a938681481 = 11;
    	a1729378197 = 1;
    	a1892947393 = 9; 
    	System.out.println("U");
    } if(((((cf && (a1729378197 == 8)) && (a310220227 == 7)) && (a299375216 == 3)) && (input.equals("O")))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 11;
    	a1892947393 = 9; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm290(String input) {
    if((((input.equals("B")) && (((a310220227 == 9) && cf) && (a299375216 == 3))) && (a1729378197 == 8))) {
    	cf = false;
    	a1729378197 = 1;
    	a1937499914 = "i";
    	a938681481 = 13; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm291(String input) {
    if(((a299375216 == 3) && ((input.equals("B")) && ((a310220227 == 10) && (cf && (a1729378197 == 8)))))) {
    	cf = false;
    	a1937499914 = "f";
    	a1729378197 = 1;
    	a938681481 = 13; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm292(String input) {
    if(((a299375216 == 3) && ((((a310220227 == 11) && cf) && (a1729378197 == 8)) && (input.equals("K"))))) {
    	cf = false;
    	a1920565083 = 8;
    	a1729378197 = 7;
    	a1668586383 = 2; 
    	System.out.println("V");
    } if(((input.equals("M")) && (((a310220227 == 11) && ((a1729378197 == 8) && cf)) && (a299375216 == 3)))) {
    	cf = false;
    	a310220227 = 14; 
    	System.out.println("W");
    } if((((a1729378197 == 8) && ((cf && (input.equals("C"))) && (a310220227 == 11))) && (a299375216 == 3))) {
    	cf = false;
    	a145848903 = "e";
    	a123124249 = "e";
    	a1729378197 = 3; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm293(String input) {
    if((((a299375216 == 3) && (((input.equals("A")) && cf) && (a1729378197 == 8))) && (a310220227 == 12))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 12;
    	a1075056448 = 8; 
    	System.out.println("R");
    } if((((input.equals("G")) && ((cf && (a1729378197 == 8)) && (a299375216 == 3))) && (a310220227 == 12))) {
    	cf = false;
    	a1039409491 = "h";
    	a299375216 = 6; 
    	System.out.println("T");
    } if(((a310220227 == 12) && ((a1729378197 == 8) && ((a299375216 == 3) && ((input.equals("J")) && cf))))) {
    	cf = false;
    	a1729378197 = 5;
    	a839019366 = "h";
    	a23351479 = 13; 
    	System.out.println("V");
    } if(((((a1729378197 == 8) && (cf && (input.equals("M")))) && (a299375216 == 3)) && (a310220227 == 12))) {
    	cf = false;
    	a1729378197 = 7;
    	a68550605 = "h";
    	a1920565083 = 14; 
    	System.out.println("P");
    } if((((input.equals("F")) && ((a1729378197 == 8) && (cf && (a299375216 == 3)))) && (a310220227 == 12))) {
    	cf = false;
    	a650861711 = "g";
    	a1729378197 = 7;
    	a1920565083 = 9; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm294(String input) {
    if(((input.equals("B")) && ((a1729378197 == 8) && ((a310220227 == 14) && (cf && (a299375216 == 3)))))) {
    	cf = false;
    	a1920565083 = 13;
    	a1729378197 = 7;
    	a1518235786 = 5; 
    	System.out.println("X");
    } if((((a1729378197 == 8) && ((input.equals("G")) && ((a299375216 == 3) && cf))) && (a310220227 == 14))) {
    	cf = false;
    	a1729378197 = 7;
    	a1920565083 = 8;
    	a1668586383 = 7; 
    	System.out.println("S");
    } if(((((cf && (a299375216 == 3)) && (a1729378197 == 8)) && (input.equals("K"))) && (a310220227 == 14))) {
    	cf = false;
    	a650861711 = "f";
    	a1729378197 = 7;
    	a1920565083 = 9; 
    	System.out.println("V");
    } 
}
private  void calculateOutputm47(String input) {
    if((cf && (a310220227 == 7))) {
    	calculateOutputm288(input);
    } 
    if((cf && (a310220227 == 9))) {
    	calculateOutputm290(input);
    } 
    if((cf && (a310220227 == 10))) {
    	calculateOutputm291(input);
    } 
    if((cf && (a310220227 == 11))) {
    	calculateOutputm292(input);
    } 
    if(((a310220227 == 12) && cf)) {
    	calculateOutputm293(input);
    } 
    if((cf && (a310220227 == 14))) {
    	calculateOutputm294(input);
    } 
}
private  void calculateOutputm295(String input) {
    if(((((a299375216 == 4) && ((a1105418891 == 6) && cf)) && (a1729378197 == 8)) && (input.equals("J")))) {
    	cf = false;
    	a1729378197 = 1;
    	a938681481 = 7;
    	a1716763601 = 6; 
    	System.out.println("U");
    } if((((a299375216 == 4) && ((input.equals("K")) && (cf && (a1729378197 == 8)))) && (a1105418891 == 6))) {
    	cf = false;
    	a1477849038 = "g";
    	a1729378197 = 2;
    	a541989745 = 3; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm296(String input) {
    if(((((input.equals("J")) && ((a1105418891 == 7) && cf)) && (a1729378197 == 8)) && (a299375216 == 4))) {
    	cf = false;
    	a1729378197 = 5;
    	a23351479 = 10;
    	a37252965 = 9; 
    	System.out.println("T");
    } if((((a1729378197 == 8) && (((a1105418891 == 7) && cf) && (input.equals("K")))) && (a299375216 == 4))) {
    	cf = false;
    	a1306585414 = "g";
    	a299375216 = 7; 
    	System.out.println("P");
    } 
}
private  void calculateOutputm297(String input) {
    if(((a1729378197 == 8) && ((a299375216 == 4) && ((input.equals("C")) && ((a1105418891 == 8) && cf))))) {
    	cf = false;
    	a1729378197 = 7;
    	a650861711 = "f";
    	a1920565083 = 9; 
    	System.out.println("T");
    } 
}
private  void calculateOutputm298(String input) {
    if(((a299375216 == 4) && (((a1729378197 == 8) && (cf && (input.equals("D")))) && (a1105418891 == 9)))) {
    	cf = false;
    	a1105418891 = 6; 
    	System.out.println("P");
    } if((((a1105418891 == 9) && ((input.equals("M")) && ((a1729378197 == 8) && cf))) && (a299375216 == 4))) {
    	cf = false;
    	a1920565083 = 11;
    	a1729378197 = 7;
    	a312388145 = 8; 
    	System.out.println("X");
    } if(((a299375216 == 4) && ((a1729378197 == 8) && (((input.equals("A")) && cf) && (a1105418891 == 9))))) {
    	cf = false;
    	a938681481 = 12;
    	a1729378197 = 1;
    	a1075056448 = 9; 
    	System.out.println("X");
    } 
}
private  void calculateOutputm299(String input) {
    if(((((a1729378197 == 8) && (cf && (a1105418891 == 10))) && (input.equals("G"))) && (a299375216 == 4))) {
    	cf = false;
    	a1477849038 = "e";
    	a674877 = "f";
    	a1729378197 = 2; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm300(String input) {
    if((((input.equals("G")) && (((a1729378197 == 8) && cf) && (a299375216 == 4))) && (a1105418891 == 11))) {
    	cf = false;
    	a1729378197 = 7;
    	a1920565083 = 13;
    	a1518235786 = 7; 
    	System.out.println("S");
    } if(((a1729378197 == 8) && ((a1105418891 == 11) && (((input.equals("K")) && cf) && (a299375216 == 4))))) {
    	cf = false;
    	a750845785 = "i";
    	a1729378197 = 7;
    	a1920565083 = 12; 
    	System.out.println("X");
    } if(((((a1729378197 == 8) && (cf && (a1105418891 == 11))) && (a299375216 == 4)) && (input.equals("M")))) {
    	cf = false;
    	a938681481 = 12;
    	a1729378197 = 1;
    	a1075056448 = 5; 
    	System.out.println("Y");
    } if(((((a299375216 == 4) && (cf && (input.equals("B")))) && (a1729378197 == 8)) && (a1105418891 == 11))) {
    	cf = false;
    	a23351479 = 12;
    	a1729378197 = 5;
    	a1803458941 = 11; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm301(String input) {
    if(((a1105418891 == 12) && ((((input.equals("L")) && cf) && (a299375216 == 4)) && (a1729378197 == 8)))) {
    	cf = false;
    	a1047798024 = "g";
    	a1729378197 = 6;
    	a23351479 = 13; 
    	System.out.println("X");
    } 
}
private  void calculateOutputm302(String input) {
    if(((a299375216 == 4) && ((input.equals("B")) && ((a1105418891 == 13) && ((a1729378197 == 8) && cf))))) {
    	cf = false;
    	a1729378197 = 7;
    	a1920565083 = 8;
    	a1668586383 = 7; 
    	System.out.println("S");
    } if((((a1729378197 == 8) && (((input.equals("G")) && cf) && (a299375216 == 4))) && (a1105418891 == 13))) {
    	cf = false;
    	a1477849038 = "e";
    	a674877 = "f";
    	a1729378197 = 2; 
    	System.out.println("T");
    } if(((input.equals("O")) && (((a1729378197 == 8) && ((a1105418891 == 13) && cf)) && (a299375216 == 4)))) {
    	cf = false;
    	a1920565083 = 8;
    	a1729378197 = 7;
    	a1668586383 = 7; 
    	System.out.println("W");
    } 
}
private  void calculateOutputm48(String input) {
    if((cf && (a1105418891 == 6))) {
    	calculateOutputm295(input);
    } 
    if(((a1105418891 == 7) && cf)) {
    	calculateOutputm296(input);
    } 
    if((cf && (a1105418891 == 8))) {
    	calculateOutputm297(input);
    } 
    if((cf && (a1105418891 == 9))) {
    	calculateOutputm298(input);
    } 
    if((cf && (a1105418891 == 10))) {
    	calculateOutputm299(input);
    } 
    if((cf && (a1105418891 == 11))) {
    	calculateOutputm300(input);
    } 
    if((cf && (a1105418891 == 12))) {
    	calculateOutputm301(input);
    } 
    if((cf && (a1105418891 == 13))) {
    	calculateOutputm302(input);
    } 
}
private  void calculateOutputm304(String input) {
    if((((((input.equals("F")) && cf) && (a1729378197 == 8)) && (a299375216 == 5)) && (a1105727296.equals("f")))) {
    	cf = false;
    	a1920565083 = 13;
    	a1729378197 = 7;
    	a1518235786 = 10; 
    	System.out.println("Y");
    } if((((input.equals("M")) && ((a1729378197 == 8) && (cf && (a1105727296.equals("f"))))) && (a299375216 == 5))) {
    	cf = false;
    	a299375216 = 3;
    	a310220227 = 9; 
    	System.out.println("U");
    } 
}
private  void calculateOutputm306(String input) {
    if(((input.equals("A")) && (((a1105727296.equals("h")) && (cf && (a299375216 == 5))) && (a1729378197 == 8)))) {
    	cf = false;
    	a1477849038 = "i";
    	a1729378197 = 4;
    	a50296898 = 11; 
    	System.out.println("P");
    } if(((input.equals("F")) && ((((a1105727296.equals("h")) && cf) && (a299375216 == 5)) && (a1729378197 == 8)))) {
    	cf = false;
    	a23351479 = 14;
    	a1729378197 = 5;
    	a871304185 = 6; 
    	System.out.println("T");
    } if((((((a299375216 == 5) && cf) && (a1105727296.equals("h"))) && (a1729378197 == 8)) && (input.equals("L")))) {
    	cf = false;
    	a1105727296 = "f"; 
    	System.out.println("Q");
    } 
}
private  void calculateOutputm49(String input) {
    if((cf && (a1105727296.equals("f")))) {
    	calculateOutputm304(input);
    } 
    if((cf && (a1105727296.equals("h")))) {
    	calculateOutputm306(input);
    } 
}
private  void calculateOutputm308(String input) {
    if(((a1039409491.equals("e")) && (((input.equals("C")) && (cf && (a1729378197 == 8))) && (a299375216 == 6)))) {
    	cf = false;
    	a938681481 = 7;
    	a1729378197 = 1;
    	a1716763601 = 5; 
    	System.out.println("Y");
    } if((((input.equals("G")) && ((a299375216 == 6) && (cf && (a1039409491.equals("e"))))) && (a1729378197 == 8))) {
    	cf = false;
    	a938681481 = 7;
    	a1729378197 = 1;
    	a1716763601 = 5; 
    	System.out.println("Y");
    } if(((((a1729378197 == 8) && (cf && (input.equals("J")))) && (a1039409491.equals("e"))) && (a299375216 == 6))) {
    	cf = false;
    	a1729378197 = 7;
    	a1920565083 = 13;
    	a1518235786 = 6; 
    	System.out.println("Y");
    } if(((input.equals("L")) && ((a299375216 == 6) && ((a1039409491.equals("e")) && ((a1729378197 == 8) && cf))))) {
    	cf = false;
    	a1114110175 = "i";
    	a1477849038 = "h";
    	a1729378197 = 4; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm309(String input) {
    if((((a1039409491.equals("f")) && ((a1729378197 == 8) && ((input.equals("D")) && cf))) && (a299375216 == 6))) {
    	cf = false;
    	a1729378197 = 7;
    	a68550605 = "f";
    	a1920565083 = 14; 
    	System.out.println("W");
    } if(((input.equals("F")) && (((a299375216 == 6) && ((a1729378197 == 8) && cf)) && (a1039409491.equals("f"))))) {
    	cf = false;
    	a1729378197 = 7;
    	a1920565083 = 8;
    	a1668586383 = 7; 
    	System.out.println("Q");
    } if(((((input.equals("H")) && (cf && (a1729378197 == 8))) && (a1039409491.equals("f"))) && (a299375216 == 6))) {
    	cf = false;
    	a1920565083 = 13;
    	a1729378197 = 7;
    	a1518235786 = 7; 
    	System.out.println("Y");
    } if((((a1039409491.equals("f")) && (((input.equals("M")) && cf) && (a299375216 == 6))) && (a1729378197 == 8))) {
    	cf = false;
    	a1729378197 = 5;
    	a23351479 = 15;
    	a948298434 = 7; 
    	System.out.println("V");
    } 
}
private  void calculateOutputm310(String input) {
    if((((a1729378197 == 8) && ((cf && (input.equals("K"))) && (a299375216 == 6))) && (a1039409491.equals("g")))) {
    	cf = false;
    	a1729378197 = 1;
    	a1937499914 = "i";
    	a938681481 = 13; 
    	System.out.println("Z");
    } 
}
private  void calculateOutputm311(String input) {
    if(((input.equals("A")) && ((a1729378197 == 8) && (((a1039409491.equals("h")) && cf) && (a299375216 == 6))))) {
    	cf = false;
    	a1306585414 = "g";
    	a299375216 = 7; 
    	System.out.println("R");
    } if(((input.equals("B")) && ((((a1039409491.equals("h")) && cf) && (a299375216 == 6)) && (a1729378197 == 8)))) {
    	cf = false;
    	a123124249 = "g";
    	a1729378197 = 3;
    	a1091978491 = 11; 
    	System.out.println("Y");
    } if((((input.equals("C")) && ((a299375216 == 6) && (cf && (a1729378197 == 8)))) && (a1039409491.equals("h")))) {
    	cf = false;
    	 
    	System.out.println("V");
    } if((((a299375216 == 6) && (((a1039409491.equals("h")) && cf) && (a1729378197 == 8))) && (input.equals("H")))) {
    	cf = false;
    	a938681481 = 10;
    	a1729378197 = 1;
    	a198422080 = 12; 
    	System.out.println("X");
    } 
}
private  void calculateOutputm312(String input) {
    if(((a1729378197 == 8) && ((((a299375216 == 6) && cf) && (input.equals("D"))) && (a1039409491.equals("i"))))) {
    	cf = false;
    	a911974320 = "i";
    	a1047798024 = "i";
    	a1729378197 = 6; 
    	System.out.println("S");
    } if((((a1729378197 == 8) && ((cf && (a299375216 == 6)) && (input.equals("F")))) && (a1039409491.equals("i")))) {
    	cf = false;
    	a299375216 = 3;
    	a310220227 = 9; 
    	System.out.println("S");
    } if(((a1039409491.equals("i")) && ((input.equals("K")) && ((cf && (a1729378197 == 8)) && (a299375216 == 6))))) {
    	cf = false;
    	a299375216 = 3;
    	a310220227 = 9; 
    	System.out.println("S");
    } 
}
private  void calculateOutputm50(String input) {
    if((cf && (a1039409491.equals("e")))) {
    	calculateOutputm308(input);
    } 
    if((cf && (a1039409491.equals("f")))) {
    	calculateOutputm309(input);
    } 
    if((cf && (a1039409491.equals("g")))) {
    	calculateOutputm310(input);
    } 
    if(((a1039409491.equals("h")) && cf)) {
    	calculateOutputm311(input);
    } 
    if(((a1039409491.equals("i")) && cf)) {
    	calculateOutputm312(input);
    } 
}
private  void calculateOutputm315(String input) {
    if(((a1306585414.equals("g")) && (((a299375216 == 7) && ((a1729378197 == 8) && cf)) && (input.equals("C"))))) {
    	cf = false;
    	 
    	System.out.println("P");
    } if(((a1729378197 == 8) && (((a299375216 == 7) && (cf && (input.equals("F")))) && (a1306585414.equals("g"))))) {
    	cf = false;
    	a938681481 = 7;
    	a1729378197 = 1;
    	a1716763601 = 5; 
    	System.out.println("Y");
    } 
}
private  void calculateOutputm51(String input) {
    if(((a1306585414.equals("g")) && cf)) {
    	calculateOutputm315(input);
    } 
}



public  void calculateOutput(String input) {
 	cf = true;
    if(((a1729378197 == 1) && cf)) {
    	if((cf && (a938681481 == 6))) {
    		calculateOutputm1(input);
    	} 
    	if(((a938681481 == 7) && cf)) {
    		calculateOutputm2(input);
    	} 
    	if((cf && (a938681481 == 8))) {
    		calculateOutputm3(input);
    	} 
    	if((cf && (a938681481 == 9))) {
    		calculateOutputm4(input);
    	} 
    	if((cf && (a938681481 == 10))) {
    		calculateOutputm5(input);
    	} 
    	if((cf && (a938681481 == 11))) {
    		calculateOutputm6(input);
    	} 
    	if((cf && (a938681481 == 12))) {
    		calculateOutputm7(input);
    	} 
    	if(((a938681481 == 13) && cf)) {
    		calculateOutputm8(input);
    	} 
    } 
    if(((a1729378197 == 2) && cf)) {
    	if(((a1477849038.equals("e")) && cf)) {
    		calculateOutputm9(input);
    	} 
    	if(((a1477849038.equals("f")) && cf)) {
    		calculateOutputm10(input);
    	} 
    	if((cf && (a1477849038.equals("g")))) {
    		calculateOutputm11(input);
    	} 
    	if(((a1477849038.equals("h")) && cf)) {
    		calculateOutputm12(input);
    	} 
    } 
    if(((a1729378197 == 3) && cf)) {
    	if((cf && (a123124249.equals("e")))) {
    		calculateOutputm14(input);
    	} 
    	if(((a123124249.equals("f")) && cf)) {
    		calculateOutputm15(input);
    	} 
    	if((cf && (a123124249.equals("g")))) {
    		calculateOutputm16(input);
    	} 
    	if((cf && (a123124249.equals("h")))) {
    		calculateOutputm17(input);
    	} 
    	if(((a123124249.equals("i")) && cf)) {
    		calculateOutputm18(input);
    	} 
    } 
    if((cf && (a1729378197 == 4))) {
    	if(((a1477849038.equals("e")) && cf)) {
    		calculateOutputm19(input);
    	} 
    	if(((a1477849038.equals("f")) && cf)) {
    		calculateOutputm20(input);
    	} 
    	if((cf && (a1477849038.equals("g")))) {
    		calculateOutputm21(input);
    	} 
    	if((cf && (a1477849038.equals("h")))) {
    		calculateOutputm22(input);
    	} 
    	if(((a1477849038.equals("i")) && cf)) {
    		calculateOutputm23(input);
    	} 
    } 
    if(((a1729378197 == 5) && cf)) {
    	if((cf && (a23351479 == 9))) {
    		calculateOutputm24(input);
    	} 
    	if((cf && (a23351479 == 10))) {
    		calculateOutputm25(input);
    	} 
    	if(((a23351479 == 11) && cf)) {
    		calculateOutputm26(input);
    	} 
    	if((cf && (a23351479 == 12))) {
    		calculateOutputm27(input);
    	} 
    	if(((a23351479 == 13) && cf)) {
    		calculateOutputm28(input);
    	} 
    	if((cf && (a23351479 == 14))) {
    		calculateOutputm29(input);
    	} 
    	if(((a23351479 == 15) && cf)) {
    		calculateOutputm30(input);
    	} 
    	if(((a23351479 == 16) && cf)) {
    		calculateOutputm31(input);
    	} 
    } 
    if((cf && (a1729378197 == 6))) {
    	if((cf && (a1047798024.equals("e")))) {
    		calculateOutputm32(input);
    	} 
    	if((cf && (a1047798024.equals("f")))) {
    		calculateOutputm33(input);
    	} 
    	if((cf && (a1047798024.equals("g")))) {
    		calculateOutputm34(input);
    	} 
    	if(((a1047798024.equals("h")) && cf)) {
    		calculateOutputm35(input);
    	} 
    	if((cf && (a1047798024.equals("i")))) {
    		calculateOutputm36(input);
    	} 
    } 
    if((cf && (a1729378197 == 7))) {
    	if(((a1920565083 == 8) && cf)) {
    		calculateOutputm37(input);
    	} 
    	if(((a1920565083 == 9) && cf)) {
    		calculateOutputm38(input);
    	} 
    	if((cf && (a1920565083 == 10))) {
    		calculateOutputm39(input);
    	} 
    	if(((a1920565083 == 11) && cf)) {
    		calculateOutputm40(input);
    	} 
    	if((cf && (a1920565083 == 12))) {
    		calculateOutputm41(input);
    	} 
    	if((cf && (a1920565083 == 13))) {
    		calculateOutputm42(input);
    	} 
    	if((cf && (a1920565083 == 14))) {
    		calculateOutputm43(input);
    	} 
    	if(((a1920565083 == 15) && cf)) {
    		calculateOutputm44(input);
    	} 
    } 
    if(((a1729378197 == 8) && cf)) {
    	if(((a299375216 == 1) && cf)) {
    		calculateOutputm45(input);
    	} 
    	if(((a299375216 == 2) && cf)) {
    		calculateOutputm46(input);
    	} 
    	if(((a299375216 == 3) && cf)) {
    		calculateOutputm47(input);
    	} 
    	if((cf && (a299375216 == 4))) {
    		calculateOutputm48(input);
    	} 
    	if((cf && (a299375216 == 5))) {
    		calculateOutputm49(input);
    	} 
    	if((cf && (a299375216 == 6))) {
    		calculateOutputm50(input);
    	} 
    	if(((a299375216 == 7) && cf)) {
    		calculateOutputm51(input);
    	} 
    } 

    errorCheck();
    if(cf)
    	throw new IllegalArgumentException("Current state has no transition for this input!");
}


public static void main(String[] args) throws Exception {
	// init system and input reader
	Problem14 eca = new Problem14();

	// main i/o-loop
	while(true) {
		//read input
		String input = stdin.readLine();

		 if((input.equals("K")) && (input.equals("L")) && (input.equals("C")) && (input.equals("F")) && (input.equals("J")) && (input.equals("I")) && (input.equals("A")) && (input.equals("G")) && (input.equals("O")) && (input.equals("H")) && (input.equals("B")) && (input.equals("D")) && (input.equals("E")) && (input.equals("N")) && (input.equals("M")))
			throw new IllegalArgumentException("Current state has no transition for this input!");
		try {
			//operate eca engine output = 
			eca.calculateOutput(input);
		} catch(IllegalArgumentException e) {
			System.err.println("Invalid input: " + e.getMessage());
		}
	}
}
}