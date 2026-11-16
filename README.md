# ElCruz - Proof of God

Argumento modal para a existência de um ser necessário. Criado em 15/11/2026.

**Status:** a dedução é válida e foi verificada por máquina. O argumento depende de uma premissa de possibilidade (P) que não pode ser provada nem refutada. Como prova de Deus, ele vale o quanto P vale.

## Definições

- **Contingente:** existe em algum mundo possível, mas não em todos.
- **Necessário:** existe em todos os mundos possíveis.
- **Explicador:** entidade que explica por que existem coisas contingentes em vez de nenhuma.

## Axiomas

Só fixam o que "explicar" significa.

- **A1.** O que explica, existe: um explicador existe no mundo em que explica.
- **A2.** Um explicador não é contingente. Se fosse, seria uma das coisas cuja existência ele deveria explicar, e a explicação pressuporia o que quer explicar.

## Premissa

- **P.** É possível que exista um explicador, isto é, em pelo menos um mundo possível alguma entidade explica a existência das coisas contingentes.

## Teorema

Existe, no mundo real, um ser necessário que é explicador em pelo menos um mundo possível.

## Prova

1. Por P, há um mundo possível *w* com um explicador *e*.
2. Por A1, *e* existe em *w*.
3. Por A2, *e* não é contingente. Como ele existe em *w*, a única forma de não ser contingente é existir em todos os mundos possíveis. Logo, *e* é necessário.
4. O mundo real é um desses mundos, então *e* existe aqui. ∎

## Notação modal

Lógica S5. □ = necessariamente, ◇ = possivelmente, E(y) = y existe, X(y) = y é explicador.

```
A1  □∀y (X(y) → E(y))
A2  □∀y (X(y) → ¬(E(y) ∧ ◇¬E(y)))
P   ◇∃y X(y)
T   ∃y (□E(y) ∧ ◇X(y))
```

## Verificação

O programa `elcruz_check.py` (mesma pasta, sem dependências) enumera todos os modelos pequenos e testa cada um:

```bash
python3 elcruz_check.py
```

Resultado da execução de 15/11/2026: 1.062.644 modelos em S5, dos quais 12.051 satisfazem A1, A2 e P.

- **Validade:** nenhum contraexemplo. A busca é prova completa, não amostragem: para refutar o teorema bastam as testemunhas que as premissas e a negação da conclusão exigem (um indivíduo, três mundos), então qualquer contraexemplo maior conteria um desse tamanho.
- **Sem colapso modal:** existe modelo que satisfaz A1, A2 e P e ainda contém coisas contingentes.
- **Sem peça redundante:** tirando A1, A2 ou P, aparece contraexemplo.
- **Dependência de S5:** sem simetria entre mundos, o explicador pode não existir no mundo real. Sem transitividade, ele pode existir aqui sem ser necessário. Os passos 3 e 4 só valem se "todos os mundos possíveis" for o mesmo conjunto visto de qualquer mundo.
- **Premissa rival:** P e "é possível um mundo sem nenhum ser necessário" nunca são verdadeiras juntas, e cada uma é consistente sozinha.

## O que o modelo não assume

- Não assume que toda coisa contingente tem explicação. Basta ser possível uma única explicação.
- Não proíbe cadeias infinitas de dependência. O argumento não usa cadeias.
- Explicar não significa tornar necessário, então coisas contingentes continuam contingentes.

## Pontos atacáveis

1. **P equivale à conclusão.** P parece modesta, mas junto com A2 ela diz "é possível um ser necessário", e em S5 isso já é "existe um ser necessário". A premissa rival leva à conclusão oposta, e o ElCruz não desempata. Ele só fixa o preço de negar P: sustentar que explicar a existência do contingente é impossível em qualquer mundo, não apenas ausente no nosso.
2. **A2.** Um crítico pode dizer que, numa cadeia infinita, cada coisa contingente é explicada pela anterior e isso basta. A resposta usual é que isso explica cada membro, mas não por que existe algum membro. A disputa segue aberta.
3. **Explicação por entidade.** P assume que quem explica é uma entidade. Se a explicação puder ser um princípio abstrato, sem entidade nenhuma, o argumento não alcança.
4. **Alcance.** O teorema não diz que esse ser explica o nosso universo, só que ele existe e que poderia explicar um. Também não diz que ele tem mente, vontade ou bondade. Se "Deus" significa apenas "ser necessário capaz de explicar o contingente", o ElCruz prova Deus a partir de P. Se significa o Deus das religiões, não prova.
