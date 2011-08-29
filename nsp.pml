
mtype = { msg1, msg2, msg3, msg4, msg5, msg6, msg7, 
	      keyA, keyB, keyI, keyS, 
	      agentA, agentB, agentI, 
	      nonceA, nonceB, nonceI};

bit statusA; 
bit statusB; 
bit statusC;

mtype partnerA;
mtype partnerB;

bit knows_nonceA = 0;
bit knows_nonceB = 0;

inline build(m, k, c1, c2) {
  m.key = k; 
  m.content1 = c1; 
  m.content2 = c2
}

inline copy(from, to) {
  to.key = from.key;
  to.content1 = from.content1;
  to.content2 = from.content2;
};

typedef Pkt { 
    mtype key, content1, content2
};

/*rede entre Alice<->Bob e Alice<->Eve*/
chan network = [0] of { mtype, mtype, Pkt}; 

/*rede entre Alice<->Servidor e Bob<->Servidor*/
chan network1 = [0] of { mtype, mtype};

/*rede entre Eve<->Bob*/
chan network2 = [0] of { mtype, mtype, Pkt};

proctype Servidor(){

	Pkt message; 


MENSAGEM2OU5:	do
	:: network1 ? (agentA,agentB) ->  build(message,keyS,keyB,agentB);
	   network ! msg2,agentA,message;
	:: network1 ? (agentA,agentI) ->  build(message,keyS,keyI,agentI); 
	   network ! msg2,agentA,message;   
	:: network1 ? (agentB,agentA) ->  build(message,keyS,keyA,agentA); 
	   network ! msg5,agentB,message;
	od;

}

proctype Alice(){
  mtype pkey;      
  mtype pnonce;   
  Pkt message;   
  Pkt data;


  statusA = 0;  

/* escolhe com quem irá iniciar o protocolo e requisita a chave para o servidor */

MENSAGEM1:  if 
  :: partnerA = agentB; network1 ! agentA,agentB;
  :: partnerA = agentI; network1 ! agentA,agentI;
  fi;

  /* espera resposta do servidor de chaves */
  network ? (msg2,agentA,data);

MENSAGEM2:  if 
  :: (data.key == keyS) -> pkey = data.content1;
  :: else -> goto FAIL;
  fi;

  /* Agora que já possui a chave de B ou I, envia msg3 para B ou I */
MENSAGEM3:  build(message,pkey,agentA,nonceA);
  network ! msg3,partnerA,message;  

  /* Aguarda resposta de B ou I */
MENSAGEM6:  network ? (msg6, agentA, data);

  /* confere os valores */ 
  if 
  :: ((data.key == keyA) && (data.content1 == nonceA)) -> goto MENSAGEM7;
  :: else -> goto FAIL;
  fi;

  /* toma conhecimento do nonce do partner*/
MENSAGEM7:  pnonce = data.content2;

  /* envia mensagem final da autenticação*/
  build(message, pkey, pnonce, 0);
  network ! msg7, partnerA, message;

end:  statusA = 1; /* fim do protocolo */

FAIL:  if
  :: statusA == 1 -> printf("protocol finished");
  :: else -> printf("FAIL state");
  fi;

}

proctype Bob(){
  mtype pkey;     
  mtype pnonce;    
  Pkt message;   
  Pkt data;   

  statusB = 0;   

  /* aguarda pela msg 3 pelos canais que possui*/
  if
  :: network ? (msg3, agentB, data) -> partnerB = data.content1; 
     pnonce = data.content2; network1 ! agentB,partnerB;
     network ? (msg5,agentB,data); 
     if
     :: (data.key == keyS) -> pkey = data.content1; goto MENSAGEM6_ALICE;
     :: else -> goto FAIL;
     fi;        

  :: network2 ? (msg3, agentB, data) -> partnerB = data.content1; 
     pnonce = data.content2; network1 ! agentB,partnerB; 
     network ? (msg5,agentB,data); 
     if
     :: (data.key == keyS) -> pkey = data.content1; goto MENSAGEM6_EVE;
     :: else -> goto FAIL;
     fi;
  fi;   

  /* Agora que já possui a chave de A ou I, envia msg6 para A ou I */
MENSAGEM6_EVE:  build(message,pkey,pnonce,nonceB);
  network2 ! msg6,partnerB,message; goto MENSAGEM7_EVE;

MENSAGEM6_ALICE:  build(message,pkey,pnonce,nonceB);
  network ! msg6,partnerB,message; goto MENSAGEM7_ALICE;

/* aguarda pela msg7*/
MENSAGEM7_EVE:  network2 ? (msg7,agentB,data);
  if 
  :: ((data.key == keyB) && (data.content1 == nonceB)) -> goto end;
  :: else -> goto FAIL;
  fi;

MENSAGEM7_ALICE:  network ? (msg7,agentB,data);
  if 
  :: ((data.key == keyB) && (data.content1 == nonceB)) -> goto end;
  :: else -> goto FAIL;
  fi;


end: statusB = 1; /* fim do protocolo */

FAIL:  if
  :: statusB == 1 -> printf("protocol finished")
  :: else -> printf("FAIL state")
  fi;

}

proctype Eve() {
  mtype tempnonce;
  mtype pkey;
  Pkt data;
  Pkt message;

  statusC = 0; 
  pkey = keyB; /*ja possui a chave publica de Bob*/

  /*escuta a rede esperando pela mensagem 3*/
LISTEN:  network ? (msg3, agentI, data);

  if
  :: ((data.key == keyI) && (data.content1 == agentA)) ->
  knows_nonceA = 1; tempnonce = data.content2;
  :: else -> goto LISTEN
  fi;

  /*constroi a mensagem se passando pelo agente A*/
  build(message,pkey,agentA,tempnonce);

  /* repassa mensagem para Bob*/
  network2 ! msg3,agentB,message;

  /* espera-se a resposta de Bob*/
MENSAGEM6BOB:  network2 ? (msg6, agentA, data);

  /* encaminha para Alice */
  copy(data, message);
MENSAGEM6ALICE:  network ! msg6,agentA,message;

  /*aguarda resposta de Alice*/
MENSAGEM7ALICE:  network ? (msg7,agentI,data);

  /* confere valores */
  if
  :: (data.key == keyI) -> tempnonce = data.content1; knows_nonceB = 1;
  :: else -> goto FAIL;
  fi;

  /* envia mensagem final do protocolo para Bob*/ 
  build(message,keyB,tempnonce,0);
MENSAGEM7BOB:  network2 ! msg7,agentB,message;

end: statusC = 1; /* fim do ataque */

assert(!statusC);

FAIL:  if
  :: statusC == 1 -> printf("protocol finished with man-in-the-middle")
  :: else -> printf("FAIL state")
  fi;

}

init{
	run Bob();
	run Eve();
	run Servidor();
	run Alice();

}


ltl p1 { []((statusB == 1) -> (statusA == 1)) };
ltl p2 { [](partnerB == agentA) };
ltl p3 { [](knows_nonceB == 0) };
ltl p4 {[](knows_nonceA -> <> knows_nonceB)}
ltl p5 {(knows_nonceA && knows_nonceB)}

