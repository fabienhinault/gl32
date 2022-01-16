outputformat := "png";
outputformatoptions := "format=rgb antialias=best";
hppp := 0.1;
vppp := 0.1;
tracingonline:=1;

def draw_arrow(expr xstart, ystart, xend, yend, margin) =
  pair v;
  v = ((xend, yend) - (xstart, ystart)) * margin / sqrt((xend - xstart)**2 + (yend - ystart)**2);
  pair rs;
  rs = (xstart, ystart) + v;
  pair re;
  re = (xend, yend) -v;
  drawarrow rs--re withpen pencircle scaled 1.5pt;
enddef;

def draw_arrow_pairs(expr pstart, pend, margin) =
  pair v;
  v = (pend - pstart) * margin / sqrt(((xpart pend) - (xpart pstart))**2 + ((ypart pend) - (ypart pstart))**2);
  pair rs;
  rs = pstart + v;
  pair re;
  re = pend -v;
  drawarrow rs--re withpen pencircle scaled 1.5pt;
enddef;

beginfig(1);
  u := 1cm;
  dot_diam_front := 4pt; 
  dot_diam_back := 0.866dot_diam_front;
  margin := 3pt;
  perspective_ratio := 0.4;
  color front_color, back_color;
  front_color := black;
  back_color := 0.4 white;
  pair O,X,Y,Z,XpY,XpZ,YpZ,XpYpZ;
  O = origin;
  X = (u, 0);
  Y = (0, u);
  Z = (0.4u, 0.4u);
  XpY = X + Y;
  XpZ = X + Z;
  YpZ = Y + Z;
  XpYpZ = X + Y + Z;
  drawdot(0, 0) withpen pencircle scaled dot_diam_front;
  drawdot(0, u) withpen pencircle scaled dot_diam_front;
  drawdot(u, 0) withpen pencircle scaled dot_diam_front;
  drawdot(u, u) withpen pencircle scaled dot_diam_front;
  drawdot(0.4u, 0.4u) withpen pencircle scaled dot_diam_back withcolor 0.4 white;
  drawdot(00.4u, u+0.4u) withpen pencircle scaled dot_diam_back withcolor 0.4 white;
  drawdot(u+0.4u, 0+0.4u) withpen pencircle scaled dot_diam_back withcolor 0.4 white;
  drawdot(u+0.4u, u+0.4u) withpen pencircle scaled dot_diam_back withcolor 0.4 white;

  %395
  %draw_arrow(u, 0, u, u, margin);
  draw_arrow_pairs(X, XpY, margin);
  draw_arrow(0, u, 0.4u, 0.4u, 3pt);
  draw_arrow(0.4u, 0.4u, 0.4u, 1.4u, margin);
  draw_arrow(u, u, 1.4u, 1.4u, margin);
  %X+Z invariant
  draw_arrow(0.4u, u+0.4u, 0, u, margin);
  draw_arrow(1.4u, 1.4u, u, 0, margin);

%  drawarrow (u, 0)--(u+0.4u, 0+0.4u) 
endfig;


end
