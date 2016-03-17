(* ::Package:: *)

Get[$MathematicaLibrary<>"/Function Library/Seven Points/flipHept.m"];

evenHeptagonLetters1=Table[Symbol["u"<>ToString[ii]],{ii,7}];
evenHeptagonLetters2=Table[1-Symbol["u"<>ToString[ii]],{ii,7}];
evenHeptagonLetters3={1 - u3*u6, 1 - u4*u7, 1 - u1*u5, 1 - u2*u6, 1 - u3*u7, 1 - u1*u4, 1 - u2*u5};
evenHeptagonLetters4={1 - u2*u5 - u4*u7, 1 - u1*u5 - u3*u6, 1 - u2*u6 - u4*u7, 1 - u1*u5 - u3*u7, 1 - u1*u4 - u2*u6, 1 - u2*u5 - u3*u7, 1 - u1*u4 - u3*u6};
evenHeptagonLetters=Join[evenHeptagonLetters1,evenHeptagonLetters2,evenHeptagonLetters3,evenHeptagonLetters4];
oddHeptagonLetters1=Table[Symbol["y1"<>ToString[ii]],{ii,7}];
oddHeptagonLetters2=Table[Symbol["y2"<>ToString[ii]],{ii,7}];
oddHeptagonLetters=Join[oddHeptagonLetters1,oddHeptagonLetters2];
heptagonLetters=Join[evenHeptagonLetters,oddHeptagonLetters];
