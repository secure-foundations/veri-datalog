node("n0").
node("n1").
node("n2").
node("n3").
node("n4").
node("n5").
node("n6").
node("n7").
node("n8").
node("n9").
node("n10").
node("n11").
node("n12").
node("n13").
node("n14").
node("n15").
node("n16").
node("n17").
node("n18").
node("n19").
node("n20").
node("n21").
node("n22").
node("n23").
node("n24").
node("n25").
node("n26").
node("n27").
node("n28").
node("n29").
node("n30").
node("n31").
node("n32").
node("n33").
node("n34").
node("n35").
node("n36").
node("n37").
node("n38").
node("n39").
node("n40").
node("n41").
node("n42").
node("n43").
node("n44").
node("n45").
node("n46").
node("n47").
node("n48").
node("n49").
node("n50").
node("n51").
node("n52").
node("n53").
node("n54").
node("n55").
node("n56").
node("n57").
node("n58").
node("n59").
node("n60").
node("n61").
node("n62").
node("n63").
node("n64").
node("n65").
node("n66").
node("n67").
node("n68").
node("n69").
node("n70").
node("n71").
node("n72").
node("n73").
node("n74").
node("n75").
node("n76").
node("n77").
node("n78").
node("n79").
node("n80").
node("n81").
node("n82").
node("n83").
node("n84").
node("n85").
node("n86").
node("n87").
node("n88").
node("n89").
node("n90").
node("n91").
node("n92").
node("n93").
node("n94").
node("n95").
node("n96").
node("n97").
node("n98").
node("n99").
node("n100").
edge("n66", "n96").
edge("n23", "n59").
edge("n49", "n50").
edge("n26", "n27").
edge("n15", "n16").
edge("n24", "n25").
edge("n11", "n12").
edge("n10", "n11").
edge("n32", "n33").
edge("n23", "n24").
edge("n64", "n74").
edge("n27", "n51").
edge("n34", "n35").
edge("n16", "n85").
edge("n17", "n62").
edge("n17", "n18").
edge("n40", "n41").
edge("n22", "n23").
edge("n18", "n69").
edge("n9", "n88").
edge("n48", "n77").
edge("n3", "n4").
edge("n39", "n40").
edge("n41", "n42").
edge("n6", "n7").
edge("n21", "n22").
edge("n18", "n19").
edge("n11", "n97").
edge("n76", "n92").
edge("n10", "n67").
edge("n45", "n72").
edge("n7", "n8").
edge("n46", "n84").
edge("n5", "n58").
edge("n31", "n32").
edge("n41", "n100").
edge("n1", "n70").
edge("n80", "n90").
edge("n13", "n78").
edge("n28", "n29").
edge("n9", "n87").
edge("n68", "n71").
edge("n18", "n55").
edge("n40", "n56").
edge("n57", "n75").
edge("n59", "n83").
edge("n35", "n36").
edge("n45", "n46").
edge("n36", "n37").
edge("n38", "n39").
edge("n43", "n44").
edge("n30", "n64").
edge("n5", "n6").
edge("n60", "n95").
edge("n2", "n3").
edge("n41", "n93").
edge("n48", "n49").
edge("n1", "n2").
edge("n11", "n52").
edge("n27", "n28").
edge("n16", "n17").
edge("n20", "n57").
edge("n86", "n89").
edge("n64", "n66").
edge("n4", "n5").
edge("n36", "n68").
edge("n65", "n91").
edge("n62", "n86").
edge("n20", "n21").
edge("n47", "n73").
edge("n21", "n81").
edge("n56", "n63").
edge("n37", "n38").
edge("n72", "n94").
edge("n9", "n10").
edge("n43", "n61").
edge("n16", "n99").
edge("n19", "n20").
edge("n50", "n98").
edge("n47", "n48").
edge("n13", "n14").
edge("n16", "n60").
edge("n46", "n82").
edge("n44", "n45").
edge("n30", "n31").
edge("n40", "n76").
edge("n14", "n15").
edge("n29", "n30").
edge("n46", "n47").
edge("n13", "n53").
edge("n8", "n9").
edge("n52", "n80").
edge("n8", "n65").
edge("n6", "n79").
edge("n12", "n13").
edge("n35", "n54").
edge("n25", "n26").
edge("n0", "n1").
edge("n42", "n43").
edge("n33", "n34").
source("n0").
destination("n50").
connected(A, B) :- edge(A, B).
connected(A, B) :- edge(A, M), connected(M, B).
go :- source(S), destination(D), connected(S,D).
